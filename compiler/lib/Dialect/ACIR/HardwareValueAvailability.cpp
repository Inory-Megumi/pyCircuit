#include "HardwareValueAvailability.h"
#include "HardwareQueueResources.h"
#include "HardwareSourceChecks.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallString.h"
#include <coroutine>
#include <cstdlib>
#include <map>
#include <memory>
#include <set>
#include <tuple>
#include <variant>

using namespace mlir;
namespace acir::ac::detail {
FailureOr<bool> hasUniformTableAvailability(
    Value value, const HardwareAnalysis &analysis,
    const std::function<LogicalResult(uint64_t, Operation *)> &debit) {
  enum class State { Active, NonUniform, Uniform };
  struct Step {
    Value first;
    Value candidate;
    bool uniform = false;
  };
  struct Frame {
    Value value;
    Value candidate;
  };
  auto classify = [&](Value current) -> Step {
    if (auto argument = dyn_cast<BlockArgument>(current)) {
      auto *owner = argument.getOwner()->getParentOp();
      if (isa<ModuleOp>(owner))
        return {.uniform = true};
      if (auto rule = dyn_cast<RuleOp>(owner))
        if (argument.getArgNumber() < rule.getCaptures().size())
          return {.first = rule.getCaptures()[argument.getArgNumber()]};
      return {};
    }

    auto *operation = current.getDefiningOp();
    if (isa_and_nonnull<SourceStateOp, TableSplatOp, InstanceOp>(operation))
      return {.uniform = true};
    if (auto collection = dyn_cast_or_null<CollectionOp>(operation))
      return {.uniform =
                  !analysis.getPrimitiveKind(analysis.resolveCallee(collection))
                       .empty()};
    if (auto rule = dyn_cast_or_null<RuleOp>(operation)) {
      if (rule->hasAttr("ac.sampled_admission"))
        return {.uniform = true};
      if (rule.getBody().hasOneBlock() && !rule.getBody().front().empty()) {
        auto yield = dyn_cast<YieldOp>(rule.getBody().front().back());
        auto ordinal = cast<OpResult>(current).getResultNumber();
        if (yield && ordinal < yield.getNumOperands())
          return {.first = yield.getOperand(ordinal)};
      }
    } else if (auto merge = dyn_cast_or_null<ValueMergeOp>(operation);
               merge && current == merge.getNext() &&
               isa<TableType>(current.getType()) &&
               merge.getGuards().size() <= 1 &&
               merge.getPaths().size() == merge.getGuards().size() &&
               merge.getValues().size() == merge.getGuards().size()) {
      bool whole = merge.getPaths().empty() ||
                   (isa<ArrayAttr>(merge.getPaths()[0]) &&
                    cast<ArrayAttr>(merge.getPaths()[0]).empty());
      if (whole)
        return {merge.getBase(), merge.getValues().empty()
                                     ? Value()
                                     : merge.getValues().front()};
    }
    return {};
  };

  // A single memo records both pending and completed values. The per-miss
  // debit still prepays the memo entry, and stack growth is paid separately.
  DenseMap<Value, State> memo;
  SmallVector<Frame, 0> pending;
  Value current = value;
  while (true) {
    Operation *site = current.getParentBlock()->getParentOp();
    if (debit && failed(debit(16, site)))
      return failure();
    auto found = memo.find(current);
    bool uniform;
    if (found != memo.end() && found->second != State::Active) {
      uniform = found->second == State::Uniform;
    } else {
      if (debit && failed(debit(64, site)))
        return failure();
      if (found != memo.end())
        return site->emitOpError() << "cycle in uniform Table availability";

      auto step = classify(current);
      if (step.first) {
        if (pending.size() == pending.capacity()) {
          if (pending.size() == pending.max_size())
            return site->emitOpError()
                   << "uniform Table availability traversal storage exhausted";
          uint64_t capacity = std::min<uint64_t>(
              pending.max_size(), 2 * uint64_t(pending.capacity()) + 1);
          if (debit && failed(debit(capacity * sizeof(Frame) + pending.size(),
                                    site)))
            return failure();
          pending.reserve(capacity);
        }
        memo.try_emplace(current, State::Active);
        pending.push_back({current, step.candidate});
        current = step.first;
        continue;
      }
      uniform = step.uniform;
      memo.try_emplace(current, uniform ? State::Uniform : State::NonUniform);
    }

    current = Value();
    while (!pending.empty()) {
      auto &parent = pending.back();
      // A whole merge only needs its candidate if its base is uniform.
      if (uniform && parent.candidate) {
        current = parent.candidate;
        parent.candidate = Value();
        break;
      }
      memo.find(parent.value)->second =
          uniform ? State::Uniform : State::NonUniform;
      pending.pop_back();
    }
    if (!current)
      return uniform;
  }
}
namespace {
// Availability proof preserves three statuses: known zero, known one, and
// unknown (X/Z). These identities do not assert raw four-state SSA equality or
// rewrite hardware predicates. Neither a | ~a nor an unknown condition becomes
// a known Boolean.
class AvailabilityProof {
  const HardwareAnalysis &analysis;
  std::function<LogicalResult(uint64_t, Operation *)> debit;
  bool charge(uint64_t units, Operation *site) {
    if (!debit || succeeded(debit(units, site))) return true;
    invalid = true;
    return false;
  }
  // A proof reads one immutable package. Keep successful declaration layouts
  // local to this invocation; another proof must revalidate the current IR.
  // Stable map values may be borrowed across matches()/coroutine suspension.
  std::map<Operation *, ModulePortLayout> portLayouts;
  const ModulePortLayout *modulePortLayout(Operation *declaration) {
    if (invalid)
      return nullptr;
    uint64_t lookup = 1;
    for (uint64_t count = portLayouts.size(); count; count >>= 1)
      lookup += 2;
    if (!charge(lookup, declaration))
      return nullptr;
    if (auto found = portLayouts.find(declaration); found != portLayouts.end())
      return &found->second;

    auto parsed = getModulePortLayout(declaration);
    if (failed(parsed)) {
      invalid = true;
      return nullptr;
    }
    // Prepay the retained node and vector capacities before insertion. Counting
    // inline capacity again is conservative; parser temporaries are unchanged.
    using Entry = decltype(portLayouts)::value_type;
    uint64_t storage =
        sizeof(Entry) + 4 * sizeof(void *) +
        uint64_t(parsed->inputValidity.capacity()) * sizeof(int64_t) +
        uint64_t(parsed->outputValidity.capacity()) * sizeof(int64_t) +
        uint64_t(parsed->routedOutputValidity.capacity()) *
            sizeof(std::pair<int64_t, int64_t>);
    if (!charge(lookup + storage, declaration))
      return nullptr;
    return &portLayouts.emplace(declaration, std::move(*parsed)).first->second;
  }
  using Expr = unsigned;
  using Uniform = std::optional<Expr>;
  using KnownGuard = std::optional<bool>;
  struct Node {
    std::string kind;
    SmallVector<Expr> children;
  };
  SmallVector<Node> nodes{{"zero", {}}, {"one", {}}};
  std::map<std::string, Expr> interned;
  bool invalid = false;
  enum class Kind {
    Availability, Formula, Raw, Row, ConstantRow, Guard, Uniform,
    WholeRows, TableElement, MergeRow, ConstantMergeRow
  };
  enum class RowMode { Raw, Availability, Formula };
  struct RowContext {
    TableMapOp map;
    Expr ordinal;
    RowContext *parent;
    unsigned depth;
  };
  using ContextOverride = std::optional<RowContext *>;

  struct QueryKey {
    Kind kind;
    Value value;
    Value index;
    RowContext *context;
    uint64_t ordinal;
    RowMode mode;
    ArrayRef<StringAttr> path;

    auto coordinates() const {
      return std::tuple(kind,
                        reinterpret_cast<uintptr_t>(value.getAsOpaquePointer()),
                        reinterpret_cast<uintptr_t>(index.getAsOpaquePointer()),
                        reinterpret_cast<uintptr_t>(context), ordinal, mode);
    }
    bool operator<(const QueryKey &other) const {
      if (coordinates() != other.coordinates())
        return coordinates() < other.coordinates();
      return std::lexicographical_compare(
          path.begin(), path.end(), other.path.begin(), other.path.end(),
          [](StringAttr left, StringAttr right) {
            return std::less<const void *>{}(left.getAsOpaquePointer(),
                                             right.getAsOpaquePointer());
          });
    }
  };

  enum class State { New, Active, Complete };
  using QueryResult = std::variant<std::monostate, Expr, Uniform, KnownGuard>;
  struct Query;
  struct Task {
    struct promise_type;
    using Handle = std::coroutine_handle<promise_type>;
    struct promise_type {
      Query &query;
      promise_type(AvailabilityProof &, Query &query) : query(query) {}
      static void *operator new(std::size_t bytes, AvailabilityProof &proof,
                                Query &query) noexcept {
        Operation *site = query.key.value.getParentBlock()->getParentOp();
        if (!proof.charge(bytes, site))
          return nullptr;
        auto *memory = std::malloc(bytes);
        if (!memory)
          proof.reject(site, "hardware availability query allocation failed");
        return memory;
      }
      static void operator delete(void *memory, std::size_t) noexcept {
        std::free(memory);
      }
      static Task get_return_object_on_allocation_failure() noexcept {
        return {};
      }
      Task get_return_object() noexcept {
        return {Handle::from_promise(*this)};
      }
      std::suspend_always initial_suspend() const noexcept { return {}; }
      std::suspend_always final_suspend() const noexcept { return {}; }
      void return_value(Expr value) noexcept { query.result = value; }
      void return_value(Uniform value) noexcept { query.result = value; }
      void return_value(KnownGuard value) noexcept { query.result = value; }
      void return_value(LogicalResult status) noexcept {
        assert(failed(status));
        (void)status;
        query.result = std::monostate();
      }
      void unhandled_exception() noexcept { std::abort(); }
    };
    // Only the query registry owns the handle. Awaiters hold query pointers.
    Handle handle{};
  };
  struct Query {
    FieldPath path;
    QueryKey key;
    State state = State::New;
    Query *parent = nullptr;
    Task::Handle handle{};
    QueryResult result;

    explicit Query(QueryKey key)
        : path(key.path.begin(), key.path.end()), key(key) {
      this->key.path = path;
    }
  };

  std::map<QueryKey, std::unique_ptr<Query>> queries;
  std::map<std::tuple<uintptr_t, Expr, uintptr_t>, RowContext> contexts;
  Query *next = nullptr;
  RowContext *activeContext = nullptr;
  std::map<std::pair<Expr, Expr>, Expr> rowReductionCache;
  std::set<std::pair<Expr, Expr>> rowReductionActive;

  RowContext *valueContext(Value value, RowContext *context) {
    auto *block = value.getParentBlock();
    // Verified TableMap bodies are isolated and have one block. Other row
    // regions are nested TableMaps with their own binding; Rules live in
    // the module body. A value outside this block cannot depend on its row.
    for (; context; context = context->parent) {
      if (!charge(1, block->getParentOp()))
        return nullptr;
      if (block == &context->map.getBody().front())
        return context;
    }
    return nullptr;
  }

  RowContext *enterRow(TableMapOp map, Expr ordinal) {
    if (!charge(1, map))
      return nullptr;
    auto key = std::tuple(
        reinterpret_cast<uintptr_t>(map.getOperation()), ordinal,
        reinterpret_cast<uintptr_t>(activeContext));
    if (auto found = contexts.find(key); found != contexts.end())
      return &found->second;
    unsigned depth = activeContext ? activeContext->depth + 1 : 1;
    if (depth > 128) {
      reject(map, "Table availability row context depth exceeds 128");
      return nullptr;
    }
    if (!charge(64 + sizeof(key) + sizeof(RowContext), map))
      return nullptr;
    return &contexts
                .try_emplace(key, RowContext{map, ordinal, activeContext, depth})
                .first->second;
  }

  Query *getQuery(Kind kind, Value value, ArrayRef<StringAttr> path,
                  uint64_t ordinal, RowMode mode, Value index,
                  ContextOverride context) {
    Operation *site = value.getParentBlock()->getParentOp();
    if (invalid || !charge(8 + path.size(), site))
      return nullptr;
    if (kind == Kind::Formula || kind == Kind::Raw ||
        (kind == Kind::Row && mode != RowMode::Availability))
      value = wire(value);
    if (invalid)
      return nullptr;
    auto *scope = context.value_or(activeContext);
    auto *valueScope = valueContext(value, scope);
    if (invalid)
      return nullptr;
    auto *indexScope = index ? valueContext(index, scope) : nullptr;
    if (indexScope && (!valueScope || indexScope->depth > valueScope->depth))
      valueScope = indexScope;
    if (invalid)
      return nullptr;

    QueryKey key{kind, value, index, valueScope, ordinal, mode, path};
    if (auto found = queries.find(key); found != queries.end())
      return found->second.get();
    if (!charge(64 + sizeof(Query) + sizeof(QueryKey) +
                    uint64_t(path.size()) * sizeof(StringAttr), site))
      return nullptr;
    auto query = std::make_unique<Query>(key);
    auto *result = query.get();
    queries.try_emplace(result->key, std::move(query));
    return result;
  }

  template <typename Result> struct Awaitable {
    AvailabilityProof &proof;
    Query *query;
    bool await_ready() const noexcept {
      return query && query->state == State::Complete;
    }
    void await_suspend(Task::Handle parent) noexcept {
      if (!query || proof.invalid)
        return;
      proof.start(*query, &parent.promise().query);
    }
    Result await_resume() const noexcept {
      assert(query && query->state == State::Complete && !proof.invalid);
      return std::get<Result>(query->result);
    }
  };

  template <typename Result = Expr>
  Awaitable<Result> request(Kind kind, Value value,
                            ArrayRef<StringAttr> path = {}, uint64_t ordinal = 0,
                            RowMode mode = RowMode::Availability,
                            Value index = {}, ContextOverride context = {}) {
    return {*this, getQuery(kind, value, path, ordinal, mode, index, context)};
  }

  Awaitable<Expr> availability(Value value, ArrayRef<StringAttr> path = {},
                                ContextOverride context = {}) {
    return request(Kind::Availability, value, path, 0, RowMode::Availability,
                   {}, context);
  }
  Awaitable<Expr> formula(Value value, ContextOverride context = {}) {
    return request(Kind::Formula, value, {}, 0, RowMode::Availability, {},
                   context);
  }
  Awaitable<Expr> rawExpression(Value value, ContextOverride context = {}) {
    return request(Kind::Raw, value, {}, 0, RowMode::Availability, {}, context);
  }
  Awaitable<Expr> rowValue(Value table, Expr ordinal, RowMode mode,
                           ArrayRef<StringAttr> path = {},
                           ContextOverride context = {}) {
    return request(Kind::Row, table, path, ordinal, mode, {}, context);
  }
  Awaitable<Expr> tableAt(Value table, uint64_t ordinal,
                          ArrayRef<StringAttr> path) {
    return request(Kind::ConstantRow, table, path, ordinal);
  }
  Awaitable<KnownGuard> knownGuard(Value value, ArrayRef<StringAttr> path = {},
                                   ContextOverride context = {}) {
    return request<KnownGuard>(Kind::Guard, value, path, 0, RowMode::Availability,
                               {}, context);
  }
  Awaitable<Uniform> uniformAvailability(Value value,
                                         ArrayRef<StringAttr> path = {},
                                         ContextOverride context = {}) {
    return request<Uniform>(Kind::Uniform, value, path, 0, RowMode::Availability,
                            {}, context);
  }
  Awaitable<Expr> wholeRows(Value table, bool available,
                             ArrayRef<StringAttr> path = {}) {
    return request(Kind::WholeRows, table, path, 0,
                   available ? RowMode::Availability : RowMode::Formula);
  }
  Awaitable<Expr> tableElement(Value table, Value index,
                                ArrayRef<StringAttr> path) {
    return request(Kind::TableElement, table, path, 0, RowMode::Availability,
                   index);
  }
  Awaitable<Expr>
  mergeRowAvailability(ValueMergeOp merge, Expr ordinal,
                       ArrayRef<StringAttr> path,
                       std::optional<uint64_t> constantOrdinal = {}) {
    if (constantOrdinal)
      return request(Kind::ConstantMergeRow, merge.getNext(), path,
                     *constantOrdinal);
    return request(Kind::MergeRow, merge.getNext(), path, ordinal);
  }

  Task evaluate(Query &query) {
    switch (query.key.kind) {
    case Kind::Availability: return evaluateAvailability(query);
    case Kind::Formula: return evaluateFormula(query);
    case Kind::Raw: return evaluateRawExpression(query);
    case Kind::Row: return evaluateRowValue(query);
    case Kind::ConstantRow: return evaluateTableAt(query);
    case Kind::Guard: return evaluateKnownGuard(query);
    case Kind::Uniform: return evaluateUniformAvailability(query);
    case Kind::WholeRows: return evaluateWholeRows(query);
    case Kind::TableElement: return evaluateTableElement(query);
    case Kind::MergeRow:
    case Kind::ConstantMergeRow: return evaluateMergeRow(query);
    }
    llvm_unreachable("unknown hardware availability query");
  }

  void start(Query &query, Query *parent) {
    if (query.state == State::Active) {
      Operation *site = query.key.value.getDefiningOp();
      if (!site)
        site = query.key.value.getParentBlock()->getParentOp();
      StringRef message = "cycle in hardware value availability";
      switch (query.key.kind) {
      case Kind::Row: message = "cycle in symbolic row availability"; break;
      case Kind::ConstantRow: message = "cycle in constant row availability"; break;
      case Kind::Uniform: message = "cycle in uniform field availability"; break;
      case Kind::Guard: message = "cycle in constant guard proof"; break;
      default: break;
      }
      reject(site, message);
      return;
    }
    assert(query.state == State::New);
    query.state = State::Active;
    query.parent = parent;
    query.handle = evaluate(query).handle;
    if (query.handle)
      next = &query;
    else
      invalid = true;
  }

  static void destroy(Query &query) {
    if (query.handle) {
      query.handle.destroy();
      query.handle = {};
    }
  }

  template <typename Result> FailureOr<Result> drive(Awaitable<Result> root) {
    assert(!activeContext && !next);
    if (invalid || !root.query)
      return failure();
    if (root.query->state == State::Complete)
      return root.await_resume();
    start(*root.query, nullptr);
    while (!invalid && next) {
      Query &query = *std::exchange(next, nullptr);
      activeContext = query.key.context;
      query.handle.resume();
      activeContext = nullptr;
      if (invalid)
        break;
      if (!query.handle.done())
        continue;
      if (std::holds_alternative<std::monostate>(query.result)) {
        invalid = true;
        break;
      }
      query.state = State::Complete;
      next = std::exchange(query.parent, nullptr);
      destroy(query);
    }
    if (invalid || root.query->state != State::Complete) {
      invalid = true;
      next = nullptr;
      return failure();
    }
    return root.await_resume();
  }
  static void appendKeyPart(std::string &key, StringRef part) {
    key += ":" + std::to_string(part.size()) + ":" + part.str();
  }
  bool inRow(Value value) {
    return activeContext &&
           value.getParentBlock() == &activeContext->map.getBody().front();
  }
  std::string valueKey(Value value, ArrayRef<StringAttr> path = {}) {
    Operation *site = value.getParentBlock()->getParentOp();
    if (!charge(32, site)) return "invalid";
    std::string key = std::to_string(reinterpret_cast<uintptr_t>(value.getAsOpaquePointer()));
    for (auto field : path) {
      if (!charge(32 + field.getValue().size(), site)) return "invalid";
      appendKeyPart(key, field.getValue());
    }
    return key;
  }
  std::string attributeKey(Attribute attr, unsigned depth = 0) {
    Operation *site = analysis.getPackage();
    if (!charge(8, site)) return "invalid";
    if (depth > 128) {
      reject(site, "row predicate attribute depth exceeds 128");
      return "invalid";
    }
    if (auto expression = dyn_cast<StaticExprAttr>(attr)) {
      // Bound and prepay the evaluator's complete input before invoking it.
      // The temporary key is private and carries no semantic authority.
      (void)attributeKey(expression.getTree(), depth + 1);
      if (invalid) return "invalid";
      if (!analysis.isStaticEvaluable(expression, {}))
        return "static:" + attributeKey(expression.getTree(), depth + 1);
      auto evaluated = analysis.evaluateStatic(expression, {}, site);
      if (failed(evaluated)) { invalid = true; return "invalid"; }
      return attributeKey(*evaluated, depth + 1);
    }
    if (auto array = dyn_cast<ArrayAttr>(attr)) {
      if (!charge(8 + array.size(), site)) return "invalid";
      std::string key = "array";
      for (Attribute element : array) {
        auto nested = attributeKey(element, depth + 1);
        if (invalid || !charge(32 + nested.size(), site)) return "invalid";
        appendKeyPart(key, nested);
      }
      return key;
    }
    if (auto dictionary = dyn_cast<DictionaryAttr>(attr)) {
      if (!charge(16 + dictionary.size(), site)) return "invalid";
      std::string key = "dictionary";
      for (NamedAttribute element : dictionary) {
        StringRef name = element.getName().strref();
        if (name == "origin" || name == "location") continue;
        if (!charge(32 + name.size(), site)) return "invalid";
        auto nested = attributeKey(element.getValue(), depth + 1);
        if (invalid || !charge(32 + nested.size(), site)) return "invalid";
        appendKeyPart(key, name);
        appendKeyPart(key, nested);
      }
      return key;
    }
    if (auto text = dyn_cast<StringAttr>(attr)) {
      if (!charge(8 + text.getValue().size(), site)) return "invalid";
      return "string:" + text.getValue().str();
    }
    if (auto integer = dyn_cast<MathIntAttr>(attr)) {
      if (!charge(8 + integer.getCanonicalValue().size(), site)) return "invalid";
      return "math:" + integer.getCanonicalValue().str();
    }
    if (auto integer = dyn_cast<IntegerAttr>(attr)) {
      if (!charge(64 + integer.getValue().getBitWidth(), site)) return "invalid";
      llvm::SmallString<32> text;
      integer.getValue().toString(text, 10, false);
      std::string type = isa<IndexType>(integer.getType()) ? "index" :
          std::to_string(unsigned(cast<IntegerType>(integer.getType()).getSignedness()));
      return "integer:" + type + ":" + std::to_string(integer.getValue().getBitWidth()) + ":" + text.str().str();
    }
    if (auto values = dyn_cast<DenseI32ArrayAttr>(attr)) {
      if (!charge(16 + 32 * uint64_t(values.size()), site)) return "invalid";
      std::string key = "i32-array";
      for (int32_t value : values.asArrayRef()) key += ":" + std::to_string(value);
      return key;
    }
    if (isa<UnitAttr>(attr)) return "unit";
    if (auto symbol = dyn_cast<FlatSymbolRefAttr>(attr)) {
      if (!charge(8 + symbol.getValue().size(), site)) return "invalid";
      return "symbol:" + symbol.getValue().str();
    }
    reject(site, "unsupported row predicate semantic attribute");
    return "invalid";
  }
  std::string typeKey(Type type, Operation *site) {
    if (auto table = dyn_cast<TableType>(type)) {
      std::string key = "table";
      appendKeyPart(key, shapeKey(table, site));
      appendKeyPart(key, typeKey(table.getElementType(), site));
      return key;
    }
    if (auto bits = dyn_cast<BitsType>(type)) {
      auto logical = attributeKey(bits.getWidth());
      if (invalid) return "invalid";
      if (!analysis.isStaticEvaluable(bits.getWidth(), {})) return "bits-template:" + logical;
      auto width = analysis.getPackedWidth(type, {}, site);
      if (failed(width)) { invalid = true; return "invalid"; }
      return "bits:" + std::to_string(*width);
    }
    if (auto structure = dyn_cast<StructType>(type)) return "struct:" + attributeKey(structure.getName());
    if (auto enumeration = dyn_cast<EnumType>(type)) return "enum:" + attributeKey(enumeration.getName());
    reject(site, "unsupported row predicate hardware type");
    return "invalid";
  }
  std::string shapeKey(TableType type, Operation *site) {
    if (!charge(16 + 32 * uint64_t(type.getShape().size()), site)) return "invalid";
    auto logical = attributeKey(type.getShape());
    if (invalid) return "invalid";
    if (!analysis.isStaticEvaluable(type.getShape(), {})) return "template:" + logical;
    auto shape = analysis.getTableShape(type, {}, site);
    if (failed(shape)) { invalid = true; return "invalid"; }
    std::string key;
    for (auto extent : *shape) key += ":" + std::to_string(extent);
    return key;
  }
  Expr rowDomain(TableType type, Operation *site) {
    return node("ordinal" + shapeKey(type, site));
  }
  Expr viewDomain(TableViewOp view, Expr ordinal) {
    std::string key = "view";
    appendKeyPart(key, view.getKind());
    appendKeyPart(key, attributeKey(view.getParameters()));
    appendKeyPart(key, shapeKey(view.getInput().getType(), view));
    appendKeyPart(key, shapeKey(view.getResult().getType(), view));
    return node(key, {ordinal});
  }
  Task evaluateRawExpression(Query &query) {
    Value value = query.key.value;
    auto *site = value.getParentBlock()->getParentOp();
    if (!inRow(value))
      co_return node("raw:" + valueKey(value) + ":" +
                       typeKey(value.getType(), site));
    auto map = activeContext->map;
    Expr row = activeContext->ordinal;
    if (auto argument = dyn_cast<BlockArgument>(value)) {
      unsigned ordinal = argument.getArgNumber();
      if (!ordinal)
        co_return node("row-ordinal:" + typeKey(value.getType(), map), {row});
      if (ordinal <= map.getTables().size())
        co_return co_await rowValue(map.getTables()[ordinal - 1], row,
                                    RowMode::Raw, {}, activeContext->parent);
      co_return co_await rawExpression(
          map.getCaptures()[ordinal - 1 - map.getTables().size()],
          activeContext->parent);
    }
    auto *op = value.getDefiningOp();
    if (!op || op->getNumRegions())
      co_return reject(op ? op : map.getOperation(),
                       "unsupported nested row predicate");
    if (!charge(32 + op->getNumOperands() + op->getAttrs().size(), op))
      co_return failure();
    SmallVector<Expr> operands;
    operands.reserve(op->getNumOperands());
    for (Value operand : op->getOperands())
      operands.push_back(co_await rawExpression(operand));
    std::string key = "row-op";
    appendKeyPart(key, op->getName().getStringRef());
    appendKeyPart(key, std::to_string(cast<OpResult>(value).getResultNumber()));
    appendKeyPart(key, typeKey(value.getType(), op));
    for (NamedAttribute attr : op->getAttrs()) {
      StringRef name = attr.getName().strref();
      if (!charge(32 + name.size(), op))
        co_return failure();
      auto semantic = attributeKey(attr.getValue());
      if (invalid || !charge(16 + semantic.size(), op))
        co_return failure();
      // Attribute payloads may contain arbitrary punctuation, including text
      // that resembles another attribute. Preserve both component boundaries.
      appendKeyPart(key, name);
      appendKeyPart(key, semantic);
    }
    co_return node(key, operands);
  }
  // Enumerate declaration paths, without asking for scalar widths or an
  // occurrence's Table geometry. Only Table-free element trees use this path.
  bool elementLeaves(Type type, FieldPath &path, SmallVector<FieldPath> &leaves,
                     DenseSet<Type> &visiting, Operation *site, unsigned depth = 0) {
    if (!charge(16 + path.size(), site)) return false;
    if (depth >= 128) {
      reject(site, "Table availability element depth exceeds 128");
      return false;
    }
    if (isa<BitsType, EnumType>(type)) {
      if (!charge(32 + path.size(), site)) return false;
      leaves.push_back(path);
      return true;
    }
    auto structure = dyn_cast<StructType>(type);
    if (!structure || !visiting.insert(type).second) {
      reject(site, "Table availability requires acyclic Table-free elements");
      return false;
    }
    llvm::scope_exit cleanup([&] { visiting.erase(type); });
    auto declaration = analysis.lookupStruct(structure);
    if (!declaration) {
      reject(site, "Table availability requires a declared Struct element");
      return false;
    }
    for (Attribute raw : declaration.getFields()) {
      auto field = cast<DictionaryAttr>(raw);
      if (!charge(16 + path.size(), site)) return false;
      path.push_back(field.getAs<StringAttr>("name"));
      bool valid = elementLeaves(field.getAs<TypeAttr>("type").getValue(), path,
                                 leaves, visiting, site, depth + 1);
      path.pop_back();
      if (!valid) return false;
    }
    return true;
  }
  Task evaluateKnownGuard(Query &query) {
    Value value = query.key.value;
    auto path = query.key.path;
    if (auto argument = dyn_cast<BlockArgument>(value)) {
      if (auto rule = dyn_cast<RuleOp>(argument.getOwner()->getParentOp()))
        co_return co_await knownGuard(rule.getCaptures()[argument.getArgNumber()],
                                      path);
      if (inRow(value)) {
        auto map = activeContext->map;
        if (argument.getArgNumber() > map.getTables().size())
          co_return co_await knownGuard(
              map.getCaptures()[argument.getArgNumber() -
                                map.getTables().size() - 1],
              path, activeContext->parent);
      }
    } else if (auto rule = value.getDefiningOp<RuleOp>()) {
      auto yield = cast<YieldOp>(rule.getBody().front().back());
      co_return co_await knownGuard(
          yield.getValues()[cast<OpResult>(value).getResultNumber()], path);
    } else if (auto get = value.getDefiningOp<StructGetOp>()) {
      if (!charge(16 + path.size(), get))
        co_return failure();
      SmallVector<StringAttr> nested{get.getFieldAttr()};
      llvm::append_range(nested, path);
      co_return co_await knownGuard(get.getValue(), nested);
    } else if (auto create = value.getDefiningOp<StructCreateOp>();
               create && !path.empty()) {
      auto declaration = analysis.lookupStruct(create.getResult().getType());
      for (auto [i, raw] : llvm::enumerate(declaration.getFields())) {
        if (!charge(4, create))
          co_return failure();
        if (cast<DictionaryAttr>(raw).getAs<StringAttr>("name") == path.front())
          co_return co_await knownGuard(create.getValues()[i],
                                        path.drop_front());
      }
    } else if (path.empty()) {
      if (auto bits = value.getDefiningOp<BitsConstantOp>()) {
        // Prepay the complete expression before static evaluation. An unbound
        // expression proves nothing and evaluation errors remain failures.
        (void)attributeKey(bits.getValue().getTree());
        if (invalid)
          co_return failure();
        if (analysis.isStaticEvaluable(bits.getValue(), {})) {
          auto evaluated = analysis.evaluateStatic(bits.getValue(), {}, bits);
          if (failed(evaluated))
            co_return failure();
          auto integer = dyn_cast<MathIntAttr>(*evaluated);
          if (!integer) {
            reject(bits, "constant guard proof requires an Integer value");
            co_return failure();
          }
          if (integer.getCanonicalValue() == "0" ||
              integer.getCanonicalValue() == "1")
            co_return KnownGuard(integer.getCanonicalValue() == "1");
        }
      } else if (auto bits = value.getDefiningOp<BitsConstant4Op>()) {
        if (bits.getPattern() == "0" || bits.getPattern() == "1")
          co_return KnownGuard(bits.getPattern() == "1");
      }
    }
    co_return KnownGuard();
  }

  Task evaluateUniformAvailability(Query &query) {
    Value value = query.key.value;
    auto path = query.key.path;
    // A scalar has exactly one availability leaf. Aggregate totality does
    // not establish equal availability of its constituent leaves.
    if (path.empty() && isa<BitsType, EnumType>(value.getType()))
      co_return Uniform(co_await availability(value));
    if (auto argument = dyn_cast<BlockArgument>(value)) {
      auto *owner = argument.getOwner()->getParentOp();
      if (isa<ModuleOp>(owner))
        co_return Uniform(co_await availability(value, path));
      if (auto rule = dyn_cast<RuleOp>(owner))
        co_return co_await uniformAvailability(
            rule.getCaptures()[argument.getArgNumber()], path);
      if (inRow(value)) {
        auto map = activeContext->map;
        unsigned ordinal = argument.getArgNumber();
        if (!ordinal)
          co_return Uniform(1);
        Value actual = ordinal <= map.getTables().size()
                           ? map.getTables()[ordinal - 1]
                           : map.getCaptures()[ordinal -
                                               map.getTables().size() - 1];
        co_return co_await uniformAvailability(actual, path,
                                               activeContext->parent);
      }
      co_return Uniform();
    }
    Operation *op = value.getDefiningOp();
    if (isa<SourceStateOp, DWireOp>(op))
      co_return Uniform(1);
    if (auto rule = dyn_cast<RuleOp>(op)) {
      if (rule->hasAttr("ac.sampled_admission"))
        co_return Uniform(co_await availability(value, path));
      auto yield = cast<YieldOp>(rule.getBody().front().back());
      co_return co_await uniformAvailability(
          yield.getValues()[cast<OpResult>(value).getResultNumber()], path);
    }
    if (isa<InstanceOp>(op))
      co_return Uniform(co_await availability(value, path));
    if (auto collection = dyn_cast<CollectionOp>(op)) {
      auto target = analysis.resolveCallee(collection);
      if (target && !analysis.getPrimitiveKind(target).empty())
        co_return Uniform(1);
      co_return Uniform();
    }
    if (auto get = dyn_cast<StructGetOp>(op)) {
      if (!charge(16 + path.size(), get))
        co_return failure();
      SmallVector<StringAttr> nested{get.getFieldAttr()};
      llvm::append_range(nested, path);
      co_return co_await uniformAvailability(get.getValue(), nested);
    }
    if (auto splat = dyn_cast<TableSplatOp>(op))
      co_return co_await uniformAvailability(splat.getInput(), path);
    if (auto view = dyn_cast<TableViewOp>(op))
      co_return co_await uniformAvailability(view.getInput(), path);
    if (auto create = dyn_cast<StructCreateOp>(op); create && !path.empty()) {
      auto declaration = analysis.lookupStruct(create.getResult().getType());
      for (auto [i, raw] : llvm::enumerate(declaration.getFields())) {
        if (!charge(4, create))
          co_return failure();
        if (cast<DictionaryAttr>(raw).getAs<StringAttr>("name") == path.front())
          co_return co_await uniformAvailability(create.getValues()[i],
                                                 path.drop_front());
      }
      co_return Uniform();
    }
    if (isa<StructCreateOp, TableCreateOp>(op)) {
      Uniform common;
      for (Value input : op->getOperands()) {
        if (!charge(4, op))
          co_return failure();
        auto constituent = co_await uniformAvailability(input, path);
        if (!constituent || (common && *common != *constituent))
          co_return Uniform();
        common = constituent;
      }
      co_return common;
    }
    if (auto merge = dyn_cast<ValueMergeOp>(op);
        merge && value == merge.getNext()) {
      if (merge.getGuards().empty() && merge.getPaths().empty() &&
          merge.getValues().empty())
        co_return co_await uniformAvailability(merge.getBase(), path);
      if (merge.getGuards().size() != 1 || merge.getPaths().size() != 1 ||
          merge.getValues().size() != 1 || !isa<ArrayAttr>(merge.getPaths()[0]) ||
          !cast<ArrayAttr>(merge.getPaths()[0]).empty())
        co_return Uniform();
      Value guard = merge.getGuards().front();
      auto known = co_await knownGuard(guard);
      if (known) {
        auto selected = co_await uniformAvailability(
            *known ? merge.getValues().front() : merge.getBase(), path);
        if (!selected)
          co_return Uniform();
        Expr available = co_await availability(guard);
        co_return Uniform(all({available, *selected}));
      }
      auto base = co_await uniformAvailability(merge.getBase(), path);
      auto candidate =
          co_await uniformAvailability(merge.getValues().front(), path);
      if (!base || !candidate)
        co_return Uniform();
      Expr available = co_await availability(guard);
      Expr condition = co_await formula(guard);
      co_return Uniform(all({available, select(condition, *candidate, *base)}));
    }
    co_return Uniform();
  }

  bool checkWholeTableMerge(ValueMergeOp merge) {
    // Whole-Table paths are empty and non-overlapping, so at most one update
    // is admitted. Even a totality shortcut must retain this structural check.
    if (merge.getGuards().size() > 1 ||
        merge.getPaths().size() != merge.getGuards().size() ||
        merge.getValues().size() != merge.getGuards().size() ||
        (!merge.getPaths().empty() &&
         (!isa<ArrayAttr>(merge.getPaths()[0]) ||
          !cast<ArrayAttr>(merge.getPaths()[0]).empty()))) {
      reject(merge, "Table availability requires a whole-value merge");
      return false;
    }
    return true;
  }
  Task evaluateMergeRow(Query &query) {
    auto merge = query.key.value.getDefiningOp<ValueMergeOp>();
    auto path = query.key.path;
    auto row = [&](Value input, ArrayRef<StringAttr> leaf) {
      if (query.key.kind == Kind::ConstantMergeRow)
        return tableAt(input, query.key.ordinal, leaf);
      return rowValue(input, query.key.ordinal, RowMode::Availability, leaf);
    };
    if (!checkWholeTableMerge(merge))
      co_return failure();
    if (merge.getGuards().empty())
      co_return co_await row(merge.getBase(), path);
    Value guardValue = merge.getGuards().front();
    auto known = co_await knownGuard(guardValue);
    if (known) {
      Expr guardAvailable = co_await availability(guardValue);
      Expr selected = co_await row(
          *known ? merge.getValues().front() : merge.getBase(), path);
      co_return all({guardAvailable, selected});
    }
    auto uniform = co_await uniformAvailability(merge.getNext(), path);
    if (uniform)
      co_return *uniform;
    SmallVector<FieldPath> leaves;
    FieldPath prefix;
    DenseSet<Type> visiting;
    if (!elementLeaves(cast<TableType>(merge.getBase().getType()).getElementType(),
                       prefix, leaves, visiting, merge))
      co_return failure();
    SmallVector<Expr> fields;
    Expr guardAvailable = co_await availability(guardValue);
    Expr guard = co_await formula(guardValue);
    for (const auto &leaf : leaves) {
      if (path.size() > leaf.size() ||
          !std::equal(path.begin(), path.end(), leaf.begin()))
        continue;
      if (!charge(8, merge))
        co_return failure();
      Expr candidate = co_await row(merge.getValues().front(), leaf);
      Expr base = co_await row(merge.getBase(), leaf);
      fields.push_back(all({guardAvailable, select(guard, candidate, base)}));
    }
    co_return all(fields);
  }
  std::optional<uint64_t> ordinalConstant(Expr ordinal) {
    StringRef kind = nodes[ordinal].kind;
    uint64_t value;
    if (kind.consume_front("constant:") && !kind.getAsInteger(10, value))
      return value;
    return std::nullopt;
  }
  Task evaluateRowValue(Query &query) {
    Value table = query.key.value;
    Expr ordinal = query.key.ordinal;
    auto mode = query.key.mode;
    auto path = query.key.path;
    // These request factories do not suspend. The selected query owns its path.
    auto element = [&](Value input, ContextOverride context = {}) {
      switch (mode) {
      case RowMode::Availability: return availability(input, path, context);
      case RowMode::Formula: return formula(input, context);
      case RowMode::Raw: return rawExpression(input, context);
      }
      llvm_unreachable("unknown Table row query mode");
    };
    if (auto argument = dyn_cast<BlockArgument>(table);
        mode == RowMode::Availability && argument &&
        isa<RuleOp>(argument.getOwner()->getParentOp())) {
      auto rule = cast<RuleOp>(argument.getOwner()->getParentOp());
      co_return co_await rowValue(rule.getCaptures()[argument.getArgNumber()],
                                  ordinal, mode, path);
    }
    if (auto rule = table.getDefiningOp<RuleOp>();
        mode == RowMode::Availability && rule) {
      if (rule->hasAttr("ac.sampled_admission"))
        co_return co_await availability(table, path);
      auto yield = cast<YieldOp>(rule.getBody().front().back());
      co_return co_await rowValue(
          yield.getValues()[cast<OpResult>(table).getResultNumber()],
          ordinal, mode, path);
    }
    if (auto splat = table.getDefiningOp<TableSplatOp>())
      co_return co_await element(splat.getInput());
    if (auto create = table.getDefiningOp<TableCreateOp>()) {
      if (!charge(8 + create.getInputs().size(), create))
        co_return failure();
      if (auto index = ordinalConstant(ordinal)) {
        if (*index >= create.getInputs().size())
          co_return mode == RowMode::Availability
                        ? 1
                        : reject(create, "row formula ordinal is out of range");
        co_return co_await element(create.getInputs()[*index]);
      }
      SmallVector<Expr> elements{ordinal};
      elements.reserve(1 + create.getInputs().size());
      for (Value input : create.getInputs())
        elements.push_back(co_await element(input));
      if (mode != RowMode::Raw &&
          llvm::all_of(ArrayRef<Expr>(elements).drop_front(),
                       [](Expr e) { return e == 1; }))
        co_return 1;
      co_return node("row-create:" + shapeKey(create.getResult().getType(),
                                              create),
                     elements);
    }
    if (auto view = table.getDefiningOp<TableViewOp>()) {
      Expr source;
      if (auto index = ordinalConstant(ordinal)) {
        auto mapped = analysis.getViewSourceOrdinal(view, *index);
        if (failed(mapped))
          co_return failure();
        source = node("constant:" + std::to_string(*mapped));
      } else {
        source = viewDomain(view, ordinal);
      }
      co_return co_await rowValue(view.getInput(), source, mode, path);
    }
    if (auto map = table.getDefiningOp<TableMapOp>()) {
      if (!charge(16 + map.getBody().front().getNumArguments(), map))
        co_return failure();
      auto *context = enterRow(map, ordinal);
      if (!context)
        co_return failure();
      Value yielded = cast<YieldOp>(map.getBody().front().getTerminator())
                          .getValues()[cast<OpResult>(table).getResultNumber()];
      co_return co_await element(yielded, context);
    }
    if (auto merge = table.getDefiningOp<ValueMergeOp>();
        merge && mode == RowMode::Availability && table == merge.getNext())
      co_return co_await mergeRowAvailability(merge, ordinal, path);
    if (mode == RowMode::Availability)
      co_return co_await availability(table, path);
    co_return node("row-source:" + valueKey(table) + ":" +
                       typeKey(cast<TableType>(table.getType()).getElementType(),
                               table.getParentBlock()->getParentOp()),
                   {ordinal});
  }
  Expr reduceRows(Expr row, Expr domain, TableType type, Operation *site,
                  unsigned depth = 0) {
    if (!charge(16, site)) return 0;
    auto key = std::make_pair(row, domain);
    if (auto found = rowReductionCache.find(key); found != rowReductionCache.end())
      return found->second;
    if (depth >= 128) return reject(site, "row reduction depth exceeds 128");
    if (!charge(64, site)) return 0;
    if (!rowReductionActive.insert(key).second)
      return reject(site, "cycle in row reduction");
    llvm::scope_exit cleanup([&] { rowReductionActive.erase(key); });
    Expr result;
    if (row == 0 || row == 1) result = row;
    // TableCreate explicitly owns each row. Only its exact ordinal domain may
    // reduce those operands; a subset/view domain cannot use this identity.
    else if (StringRef(nodes[row].kind).starts_with("row-create:") &&
             nodes[row].children.front() == domain)
      result = all(ArrayRef<Expr>(nodes[row].children).drop_front());
    else if (nodes[row].kind == "and") {
      // AND over rows distributes over per-row AND in four-state semantics.
      // Keep selections inside the row: moving a select across this reduction
      // would incorrectly equate complementary partial fields at selector X.
      if (!charge(16 + 8 * uint64_t(nodes[row].children.size()), site)) return 0;
      SmallVector<Expr> children(nodes[row].children);
      SmallVector<Expr> reduced;
      reduced.reserve(children.size());
      for (Expr child : children) {
        reduced.push_back(reduceRows(child, domain, type, site, depth + 1));
        if (invalid) return 0;
      }
      result = all(reduced);
    } else {
      // A broadcast over the real nonempty domain reduces to the same scalar.
      SmallVector<Expr> pending{row};
      DenseSet<Expr> seen;
      bool dependent = false;
      while (!pending.empty()) {
        Expr current = pending.pop_back_val();
        if (!charge(4 + nodes[current].children.size(), site)) return 0;
        if (current == domain) { dependent = true; break; }
        if (!seen.insert(current).second) continue;
        llvm::append_range(pending, nodes[current].children);
      }
      result = dependent ? node("fold-and" + shapeKey(type, site), {row}) : row;
    }
    if (!invalid) rowReductionCache.emplace(key, result);
    return result;
  }
  Task evaluateWholeRows(Query &query) {
    Value table = query.key.value;
    auto type = cast<TableType>(table.getType());
    Operation *site = table.getParentBlock()->getParentOp();
    Expr domain = rowDomain(type, site);
    Expr row =
        co_await rowValue(table, domain, query.key.mode, query.key.path);
    co_return reduceRows(row, domain, type, site);
  }

  Expr node(StringRef kind, ArrayRef<Expr> children = {}) {
    if (!charge(1 + kind.size() + children.size(), analysis.getPackage())) return 0;
    // Kind text contains semantic strings; it must not absorb child IDs.
    std::string key;
    appendKeyPart(key, kind);
    for (auto child : children)
      key += ":" + std::to_string(child);
    auto [entry, inserted] = interned.emplace(key, nodes.size());
    if (inserted)
      nodes.push_back({kind.str(), SmallVector<Expr>(children)});
    return entry->second;
  }
  Expr all(ArrayRef<Expr> inputs) {
    SmallVector<Expr> terms;
    for (auto input : inputs) {
      if (input == 0)
        return 0;
      if (input == 1)
        continue;
      if (nodes[input].kind == "and")
        llvm::append_range(terms, nodes[input].children);
      else
        terms.push_back(input);
    }
    llvm::sort(terms);
    terms.erase(std::unique(terms.begin(), terms.end()), terms.end());
    if (terms.empty())
      return 1;
    if (terms.size() == 1)
      return terms.front();
    return node("and", terms);
  }
  Expr select(Expr condition, Expr yes, Expr no) {
    if (condition == 1 || yes == no)
      return yes;
    if (condition == 0)
      return no;
    if (yes == 1 && no == 0)
      return condition;
    return node("select", {condition, yes, no});
  }
  Value wire(Value value) {
    DenseSet<Value> seen;
    while (seen.insert(value).second) {
      if (auto arg = dyn_cast<BlockArgument>(value)) {
        if (auto rule = dyn_cast<RuleOp>(arg.getOwner()->getParentOp())) {
          value = rule.getCaptures()[arg.getArgNumber()];
          continue;
        }
      } else if (auto rule = value.getDefiningOp<RuleOp>()) {
        value = cast<YieldOp>(rule.getBody().front().back())
                    .getValues()[cast<OpResult>(value).getResultNumber()];
        continue;
      }
      return value;
    }
    invalid = true;
    return value;
  }
  std::optional<std::string> constant(Value value) {
    auto op = wire(value).getDefiningOp<BitsConstantOp>();
    if (!op)
      return std::nullopt;
    auto tree = op.getValue().getTree();
    auto literal = tree.getAs<DictionaryAttr>("value");
    auto integer =
        literal ? literal.getAs<MathIntAttr>("value") : MathIntAttr();
    if (!integer)
      return std::nullopt;
    return integer.getCanonicalValue().str();
  }
  Expr scalar(Value value) {
    value = wire(value);
    if (auto number = constant(value))
      return node("constant:" + *number);
    return node("wire:" + std::to_string(reinterpret_cast<uintptr_t>(
                              value.getAsOpaquePointer())));
  }
  Expr equal(Expr left, Expr right) {
    if (left > right)
      std::swap(left, right);
    return node("eq", {left, right});
  }
  Task evaluateFormula(Query &query) {
    Value value = query.key.value;
    KnownGuard known;
    if (isa_and_nonnull<BitsConstantOp, BitsConstant4Op, StructGetOp>(
            value.getDefiningOp()))
      known = co_await knownGuard(value);
    if (known)
      co_return *known ? 1 : 0;
    if (auto number = constant(value);
        number && (*number == "0" || *number == "1"))
      co_return *number == "1" ? 1 : 0;
    if (auto get = value.getDefiningOp<TableGetOp>();
        get && value == get->getResult(0)) {
      if (auto number = constant(get.getIndex())) {
        uint64_t ordinal;
        auto type = cast<TableType>(get.getInput().getType());
        if (StringRef(*number).getAsInteger(10, ordinal) ||
            !analysis.isStaticEvaluable(type.getShape(), {}))
          co_return scalar(value);
        // An out-of-range TableGet payload is X. Only an in-range constant
        // row can replace the raw payload expression.
        (void)shapeKey(type, get);
        if (invalid)
          co_return failure();
        auto size = analysis.getTableSize(type, {}, get);
        if (failed(size))
          co_return failure();
        if (ordinal >= *size)
          co_return scalar(value);
        Expr index = node("constant:" + std::to_string(ordinal));
        co_return co_await rowValue(get.getInput(), index, RowMode::Formula);
      }
    }
    if (auto fold = value.getDefiningOp<TableFoldOp>();
        fold && fold.getKind() == "and")
      co_return co_await wholeRows(fold.getInput(), false);
    if (inRow(value) && isa<BlockArgument>(value)) {
      auto map = activeContext->map;
      auto ordinal = cast<BlockArgument>(value).getArgNumber();
      if (!ordinal)
        co_return co_await rawExpression(value);
      if (ordinal <= map.getTables().size())
        co_return co_await rowValue(map.getTables()[ordinal - 1],
                                    activeContext->ordinal, RowMode::Formula,
                                    {}, activeContext->parent);
      co_return co_await formula(
          map.getCaptures()[ordinal - 1 - map.getTables().size()],
          activeContext->parent);
    }
    if (auto op = value.getDefiningOp<BitsBinaryOp>();
        op && op.getOpcode() == "and") {
      Expr left = co_await formula(op->getOperand(0));
      Expr right = co_await formula(op->getOperand(1));
      co_return all({left, right});
    }
    if (auto op = value.getDefiningOp<BitsSelectOp>()) {
      Expr condition = co_await formula(op.getCondition());
      Expr yes = co_await formula(op.getTrueValue());
      Expr no = co_await formula(op.getFalseValue());
      co_return select(condition, yes, no);
    }
    if (auto op = value.getDefiningOp<ValueRequireOp>()) {
      Expr path = co_await formula(op.getPath());
      Expr available = co_await formula(op.getAvailability());
      co_return select(path, available, 1);
    }
    if (auto op = value.getDefiningOp<BitsCompareOp>()) {
      if (inRow(value))
        co_return co_await rawExpression(value);
      auto left = constant(op->getOperand(0));
      auto right = constant(op->getOperand(1));
      StringRef predicate = op.getPredicate();
      if (left && right &&
          (predicate == "eq" || predicate == "case_eq" || predicate == "ne"))
        co_return ((*left == *right) != (predicate == "ne")) ? 1 : 0;
      if (predicate == "eq")
        co_return equal(scalar(op->getOperand(0)), scalar(op->getOperand(1)));
      co_return scalar(value);
    }
    if (inRow(value))
      co_return co_await rawExpression(value);
    co_return scalar(value);
  }
  Expr reject(Operation *site, StringRef message) {
    site->emitOpError() << message;
    invalid = true;
    return 0;
  }
  Task evaluateTableAt(Query &query) {
    Value table = query.key.value;
    uint64_t ordinal = query.key.ordinal;
    auto path = query.key.path;
    if (auto arg = dyn_cast<BlockArgument>(table))
      if (auto rule = dyn_cast<RuleOp>(arg.getOwner()->getParentOp()))
        co_return co_await tableAt(rule.getCaptures()[arg.getArgNumber()],
                                   ordinal, path);
    if (auto rule = table.getDefiningOp<RuleOp>()) {
      if (rule->hasAttr("ac.sampled_admission"))
        co_return co_await availability(table, path);
      auto yield = cast<YieldOp>(rule.getBody().front().back());
      co_return co_await tableAt(
          yield.getValues()[cast<OpResult>(table).getResultNumber()], ordinal,
          path);
    }
    if (auto merge = table.getDefiningOp<ValueMergeOp>();
        merge && table == merge.getNext())
      co_return co_await mergeRowAvailability(merge, 0, path, ordinal);
    if (auto splat = table.getDefiningOp<TableSplatOp>())
      co_return co_await availability(splat.getInput(), path);
    if (auto view = table.getDefiningOp<TableViewOp>()) {
      auto source = analysis.getViewSourceOrdinal(view, ordinal);
      if (failed(source))
        co_return failure();
      co_return co_await tableAt(view.getInput(), *source, path);
    }
    if (auto create = table.getDefiningOp<TableCreateOp>()) {
      if (ordinal >= create.getInputs().size())
        co_return 1;
      co_return co_await availability(create.getInputs()[ordinal], path);
    }
    if (auto map = table.getDefiningOp<TableMapOp>()) {
      bool total = true;
      for (Value input : map->getOperands())
        if ((co_await availability(input)) != 1) {
          total = false;
          break;
        }
      if (total)
        co_return 1;
      Expr index = node("constant:" + std::to_string(ordinal));
      co_return co_await rowValue(table, index, RowMode::Availability, path);
    }
    co_return co_await availability(table, path);
  }

  Task evaluateTableElement(Query &query) {
    Value table = query.key.value;
    Value index = query.key.index;
    auto path = query.key.path;
    auto size = analysis.getTableSize(cast<TableType>(table.getType()), {},
                                      table.getParentRegion()->getParentOp());
    if (failed(size))
      co_return failure();
    auto indexWidth = analysis.getPackedWidth(
        index.getType(), {}, index.getParentRegion()->getParentOp());
    if (failed(indexWidth))
      co_return failure();
    // Ordinals outside the index carrier cannot be selected. In particular,
    // a Bits1 index into three rows never compares against a truncated two.
    if (*indexWidth < 64)
      *size = std::min(*size, uint64_t(1) << *indexWidth);
    if (auto number = constant(index)) {
      uint64_t ordinal;
      if (!StringRef(*number).getAsInteger(10, ordinal)) {
        // An out-of-range index does not introduce a new range guard.
        if (ordinal >= *size)
          co_return 1;
        co_return co_await tableAt(table, ordinal, path);
      }
    }
    Expr selected = 1;
    for (uint64_t i = *size; i-- > 0;) {
      Expr match = equal(scalar(index), node("constant:" + std::to_string(i)));
      Expr row = co_await tableAt(table, i, path);
      selected = select(match, row, selected);
    }
    co_return selected;
  }

  Task evaluateAvailability(Query &query) {
    Value value = query.key.value;
    auto path = query.key.path;
    if (auto arg = dyn_cast<BlockArgument>(value)) {
      auto *owner = arg.getOwner()->getParentOp();
      if (inRow(arg)) {
        auto map = activeContext->map;
        unsigned ordinal = arg.getArgNumber();
        if (!ordinal)
          co_return 1;
        if (ordinal <= map.getTables().size())
          co_return co_await rowValue(
              map.getTables()[ordinal - 1], activeContext->ordinal,
              RowMode::Availability, path, activeContext->parent);
        co_return co_await availability(
            map.getCaptures()[ordinal - 1 - map.getTables().size()], path,
            activeContext->parent);
      }
      if (auto rule = dyn_cast<RuleOp>(owner))
        co_return co_await availability(rule.getCaptures()[arg.getArgNumber()],
                                         path);
      if (auto module = dyn_cast<ModuleOp>(owner)) {
        auto ports = modulePortLayout(module);
        if (!ports)
          co_return failure();
        unsigned ordinal = arg.getArgNumber();
        if (ordinal < ports->inputValidity.size() &&
            ports->inputValidity[ordinal] >= 0)
          co_return co_await formula(
              arg.getOwner()->getArgument(ports->inputValidity[ordinal]));
        // These internal lanes are authenticated against the actual producer
        // Rule and its entire fire by verifyTransactionReturns. Availability
        // follows the return companion across each hierarchy boundary.
        if (auto returns = module->getAttrOfType<DictionaryAttr>("ac.transaction_returns"))
          if (auto incoming = returns.getAs<ArrayAttr>("incoming"))
            for (Attribute raw : incoming) {
              if (!charge(1, module))
                co_return failure();
              auto row = dyn_cast<DictionaryAttr>(raw);
              auto data = row ? row.getAs<IntegerAttr>("data") : IntegerAttr();
              auto enable = row ? row.getAs<IntegerAttr>("enable") : IntegerAttr();
              if (!data || !enable || data.getInt() < 0 || enable.getInt() < 0 ||
                  uint64_t(enable.getInt()) >= arg.getOwner()->getNumArguments())
                co_return reject(
                    module, "invalid transaction return availability lane");
              if (uint64_t(data.getInt()) == ordinal)
                co_return co_await formula(
                    arg.getOwner()->getArgument(enable.getInt()));
            }
        co_return 1;
      }
      co_return reject(owner,
                    "availability has unsupported region argument provenance");
    }
    Operation *op = value.getDefiningOp();
    if (inRow(value) && op->getNumRegions())
      co_return reject(op, "availability has unsupported nested row regions");
    if (isa<BitsConstantOp, BitsConstant4Op, EnumCreateOp, SourceStateOp, DWireOp>(op))
      co_return 1;
    if (auto rule = dyn_cast<RuleOp>(op)) {
      auto yields = cast<YieldOp>(rule.getBody().front().back()).getValues();
      auto sampled =
          rule->getAttrOfType<DictionaryAttr>("ac.sampled_admission");
      if (sampled) {
        auto fire = sampled.getAs<IntegerAttr>("fire_result");
        if (!fire || fire.getInt() < 0 ||
            uint64_t(fire.getInt()) >= yields.size())
          co_return reject(rule,
                        "availability requires a valid sampled fire result");
        uint64_t ordinary = fire.getInt();
        auto module = rule->getParentOfType<ModuleOp>();
        auto wiring =
            module->getAttrOfType<DictionaryAttr>("ac.transaction_wiring");
        auto writers =
            wiring ? wiring.getAs<ArrayAttr>("writers") : ArrayAttr();
        if (writers)
          for (auto raw : writers) {
            auto writer = dyn_cast<DictionaryAttr>(raw);
            if (writer &&
                writer.get("registration") == rule->getAttr("occurrence")) {
              auto count = writer.getAs<IntegerAttr>("ordinary_results");
              if (!count || count.getInt() < 0)
                co_return reject(
                    rule, "availability requires valid ordinary result count");
              ordinary = count.getInt();
            }
          }
        // Candidate D/E and check witnesses have private routing
        // proofs. They are not authored payload outputs and must not acquire a
        // producer-fire prerequisite merely by being transported internally.
        if (cast<OpResult>(value).getResultNumber() >= ordinary)
          co_return 1;
        co_return co_await formula(yields[fire.getInt()]);
      }
      co_return co_await availability(
          yields[cast<OpResult>(value).getResultNumber()], path);
    }
    if (auto instance = dyn_cast<InstanceOp>(op)) {
      Operation *target = analysis.lookupDefinition(instance.getCallee());
      if (!target)
        co_return reject(instance, "availability has an unresolved instance");
      if (!analysis.getPrimitiveKind(target).empty())
        co_return 1;
      if (isa<ModuleImportOp>(target) && target->hasAttr("ac.external_contract")) {
        // Availability includes every declared input, independently of payload
        // dependency_summary. Empty-input externs are total.
        SmallVector<Expr> inputs;
        for (Value input : instance.getInputs())
          inputs.push_back(co_await availability(input));
        co_return all(inputs);
      }
      auto ports = modulePortLayout(target);
      if (!ports)
        co_return failure();
      auto ordinal = cast<OpResult>(value).getResultNumber();
      if (ordinal < ports->outputValidity.size() &&
          ports->outputValidity[ordinal] >= 0)
        co_return co_await formula(
            instance->getResult(ports->outputValidity[ordinal]));
      for (auto [payload, companion] : ports->routedOutputValidity)
        if (payload == ordinal)
          co_return co_await formula(instance->getResult(companion));
      co_return 1;
    }
    if (auto collection = dyn_cast<CollectionOp>(op)) {
      auto target = analysis.lookupDefinition(collection.getCallee());
      if (target && !analysis.getPrimitiveKind(target).empty())
        co_return 1;
      if (target) {
        auto ports = modulePortLayout(target);
        if (!ports)
          co_return failure();
        if (llvm::all_of(ports->inputValidity,
                         [](int64_t i) { return i < 0; }) &&
            llvm::all_of(ports->outputValidity,
                         [](int64_t i) { return i < 0; })) {
          bool total = true;
          for (Value input : collection->getOperands())
            if ((co_await availability(input)) != 1) {
              total = false;
              break;
            }
          if (total)
            co_return 1;
        }
      }
      co_return reject(collection, "availability requires scalar instance "
                                   "routing for ordinary Collections");
    }
    if (auto get = dyn_cast<StructGetOp>(op)) {
      SmallVector<StringAttr> nested{get.getFieldAttr()};
      llvm::append_range(nested, path);
      co_return co_await availability(get.getValue(), nested);
    }
    if (auto create = dyn_cast<StructCreateOp>(op)) {
      if (!path.empty()) {
        auto declaration = analysis.lookupStruct(create.getResult().getType());
        for (auto [i, raw] : llvm::enumerate(declaration.getFields()))
          if (cast<DictionaryAttr>(raw).getAs<StringAttr>("name") ==
              path.front())
            co_return co_await availability(create.getValues()[i],
                                             path.drop_front());
        co_return reject(create,
                      "availability projection names an unknown Struct field");
      }
    }
    if (auto selectOp = dyn_cast<BitsSelectOp>(op)) {
      Value condition = selectOp.getCondition();
      Expr guardAvailable = co_await availability(condition);
      Expr guard = co_await formula(condition);
      Expr yes = co_await availability(selectOp.getTrueValue(), path);
      Expr no = co_await availability(selectOp.getFalseValue(), path);
      co_return all({guardAvailable, select(guard, yes, no)});
    }
    if (auto merge = dyn_cast<ValueMergeOp>(op)) {
      if (cast<OpResult>(value).getResultNumber() == 1) {
        SmallVector<Expr> guards;
        for (Value guard : merge.getGuards())
          guards.push_back(co_await availability(guard));
        co_return all(guards);
      }
      if (isa<TableType>(value.getType()) && !checkWholeTableMerge(merge))
        co_return failure();
      if (merge.getGuards().empty() && merge.getPaths().empty() &&
          merge.getValues().empty())
        co_return co_await availability(merge.getBase(), path);
      if (merge.getGuards().size() == 1 && merge.getPaths().size() == 1 &&
          merge.getValues().size() == 1 && isa<ArrayAttr>(merge.getPaths()[0]) &&
          cast<ArrayAttr>(merge.getPaths()[0]).empty()) {
        Value guard = merge.getGuards().front();
        auto known = co_await knownGuard(guard);
        if (known) {
          Expr guardAvailable = co_await availability(guard);
          Expr selected = co_await availability(
              *known ? merge.getValues().front() : merge.getBase(), path);
          co_return all({guardAvailable, selected});
        }
      }
      if (isa<TableType>(value.getType())) {
        auto uniform = co_await uniformAvailability(value, path);
        if (uniform)
          co_return *uniform;
        co_return co_await wholeRows(value, true, path);
      }
      auto leaves = analysis.getFieldPaths(merge.getBase().getType(), {}, merge,
                                           debit);
      if (failed(leaves))
        co_return failure();
      SmallVector<Expr> fields;
      for (const auto &leaf : *leaves) {
        if (path.size() > leaf.size() ||
            !std::equal(path.begin(), path.end(), leaf.begin()))
          continue;
        Expr available = co_await availability(merge.getBase(), leaf);
        for (auto [i, raw] : llvm::enumerate(merge.getPaths())) {
          auto suffix = cast<ArrayAttr>(raw);
          if (suffix.size() > leaf.size() ||
              !std::equal(suffix.begin(), suffix.end(), leaf.begin()))
            continue;
          Value guard = merge.getGuards()[i];
          Expr guardAvailable = co_await availability(guard);
          Expr condition = co_await formula(guard);
          Expr candidate = co_await availability(
              merge.getValues()[i],
              ArrayRef<StringAttr>(leaf).drop_front(suffix.size()));
          available = all({guardAvailable,
                           select(condition, candidate, available)});
        }
        fields.push_back(available);
      }
      co_return all(fields);
    }
    if (auto splat = dyn_cast<TableSplatOp>(op))
      co_return co_await availability(splat.getInput(), path);
    if (auto create = dyn_cast<TableCreateOp>(op)) {
      SmallVector<Expr> inputs;
      for (Value input : create.getInputs())
        inputs.push_back(co_await availability(input, path));
      co_return all(inputs);
    }
    if (isa<TableMapOp, TableViewOp>(op)) {
      for (Value input : op->getOperands())
        if ((co_await availability(input)) != 1)
          co_return co_await wholeRows(value, true, path);
      co_return 1;
    }
    if (auto read = dyn_cast<TableReadOp>(op)) {
      auto uniform = hasUniformTableAvailability(read.getInput(), analysis,
                                                 debit);
      if (failed(uniform))
        co_return failure();
      Expr selected;
      if (*uniform)
        selected = co_await tableAt(read.getInput(), 0, path);
      else
        selected = co_await tableElement(read.getInput(), read.getIndex(), path);
      Expr index = co_await availability(read.getIndex());
      co_return all({index, selected});
    }
    if (auto get = dyn_cast<TableGetOp>(op)) {
      Expr index = co_await availability(get.getIndex());
      if (cast<OpResult>(value).getResultNumber() == 1)
        co_return index;
      Expr selected =
          co_await tableElement(get.getInput(), get.getIndex(), path);
      co_return all({index, selected});
    }
    if (auto require = dyn_cast<ValueRequireOp>(op)) {
      Expr available = co_await availability(require.getAvailability());
      Expr pathAvailable = co_await availability(require.getPath());
      co_return all({available, pathAvailable});
    }
    if (op->getNumRegions()) {
      bool total = true;
      for (Value input : op->getOperands())
        if ((co_await availability(input)) != 1) {
          total = false;
          break;
        }
      if (total && isa<TableMapOp, TableMatchOp>(op))
        co_return 1;
      co_return reject(op, "availability requires normalized region provenance");
    }
    SmallVector<Expr> operands;
    for (Value operand : op->getOperands())
      operands.push_back(co_await availability(operand, path));
    co_return all(operands);
  }
  LogicalResult matches(Value payload, Value supplied, Operation *site) {
    auto actual = drive(availability(payload));
    if (succeeded(actual)) {
      auto expected = supplied ? drive(formula(supplied)) : FailureOr<Expr>(1);
      if (succeeded(expected) && *actual == *expected)
        return success();
    }
    return site->emitOpError() << "availability differs from actual payload SSA";
  }

public:
  explicit AvailabilityProof(
      const HardwareAnalysis &analysis,
      const std::function<LogicalResult(uint64_t, Operation *)> &debit = {})
      : analysis(analysis), debit(debit) {}
  ~AvailabilityProof() {
    for (auto &entry : queries)
      destroy(*entry.second);
  }

  LogicalResult run() {
    std::optional<DenseSet<OpOperand *>> queueUses;
    for (auto module : analysis.getDefinitions()) {
      auto ports = modulePortLayout(module);
      if (!ports)
        return failure();
      auto yield = cast<YieldOp>(module.getBody().front().back());
      auto yielded = yield.getValues();
      DenseMap<unsigned, unsigned> companions;
      DenseSet<unsigned> controls;
      for (auto [payload, companion] : llvm::enumerate(ports->outputValidity))
        if (companion >= 0) {
          companions.try_emplace(payload, companion);
          controls.insert(companion);
        }
      for (auto [payload, companion] : ports->routedOutputValidity) {
        companions.try_emplace(payload, companion);
        controls.insert(companion);
      }
      DenseSet<unsigned> queueSummaries;
      auto queueWiring = module->getAttrOfType<DictionaryAttr>("ac.queue_wiring");
      if (queueWiring && queueWiring.get("pop_summaries")) {
        // Queue summaries are private control outputs, even when their exact
        // subtree union is an authored public input. Authenticate the actual
        // yield edge, not the shared SSA value. This structural collector never
        // calls sampled-admission or availability proof, so there is no proof
        // recursion through Rule fire/private-route validation.
        if (!queueUses) {
          auto verified = getVerifiedQueueResourceUses(analysis);
          if (failed(verified)) return failure();
          queueUses = std::move(*verified);
        }
        auto rows = queueWiring.getAs<ArrayAttr>("pop_summaries");
        if (!rows || rows.empty()) return failure();
        for (Attribute raw : rows) {
          auto row = dyn_cast<DictionaryAttr>(raw);
          auto output = row ? row.getAs<IntegerAttr>("output") : IntegerAttr();
          if (!row || row.size() != 2 || !row.getAs<DictionaryAttr>("queue") ||
              !output || !output.getType().isSignlessInteger(64) || output.getInt() < 0 ||
              uint64_t(output.getInt()) < ports->sourceOutputCount ||
              uint64_t(output.getInt()) >= yielded.size())
            return module->emitOpError() << "private Queue summary requires its authenticated output ordinal";
          unsigned ordinal = output.getInt();
          if (controls.contains(ordinal) || companions.count(ordinal) ||
              !queueSummaries.insert(ordinal).second ||
              !queueUses->contains(&yield->getOpOperand(ordinal)))
            return module->emitOpError() << "private Queue summary cannot replace public or routed payload availability";
        }
      }
      // Private lexical capture exports also require actual yielded-SSA proof.
      // An unmapped payload is permitted only when that proof establishes
      // totality. Only separately authenticated private Queue summary edges
      // bypass this payload check; other uses of the same value remain checked.
      for (unsigned i = 0; i < yielded.size(); ++i) {
        if (controls.contains(i) || queueSummaries.contains(i))
          continue;
        auto companion = companions.find(i);
        Value supplied = companion == companions.end()
                             ? Value()
                             : yielded[companion->second];
        if (failed(matches(yielded[i], supplied, module)))
          return failure();
      }
      auto result = module.walk([&](Operation *operation) {
        if (auto require = dyn_cast<ValueRequireOp>(operation))
          return failed(matches(require.getPayload(), require.getAvailability(),
                                require))
                     ? WalkResult::interrupt()
                     : WalkResult::advance();
        if (auto collection = dyn_cast<CollectionOp>(operation)) {
          auto *target = analysis.resolveCallee(collection);
          if (target && isa<ModuleImportOp>(target) &&
              target->hasAttr("ac.external_contract")) {
            for (Value output : collection.getOutputs())
              if (failed(drive(availability(output))))
                return WalkResult::interrupt();
            // Result-free extern Collections still cannot bypass the current
            // total-input admission limitation.
            for (Value input : collection.getInputs()) {
              auto available = drive(availability(input));
              if (failed(available) || *available != 1) {
                collection.emitOpError()
                    << "availability requires scalar instance routing for ordinary Collections";
                return WalkResult::interrupt();
              }
            }
          }
        }
        auto instance = dyn_cast<InstanceOp>(operation);
        if (!instance)
          return WalkResult::advance();
        auto *target = analysis.lookupDefinition(instance.getCallee());
        if (!target)
          return WalkResult::interrupt();
        if (!analysis.getPrimitiveKind(target).empty())
          return WalkResult::advance();
        if (isa<ModuleImportOp>(target) && target->hasAttr("ac.external_contract")) {
          // An extern accepts partial inputs. Its outputs derive their own
          // all-input availability, including dead outputs and cycles.
          for (Value output : instance.getOutputs())
            if (failed(drive(availability(output))))
              return WalkResult::interrupt();
          return WalkResult::advance();
        }
        auto layout = modulePortLayout(target);
        if (!layout)
          return WalkResult::interrupt();
        for (unsigned i = 0; i < layout->sourceInputCount; ++i) {
          int64_t companion = layout->inputValidity[i];
          if (failed(matches(instance->getOperand(i),
                             companion < 0 ? Value()
                                           : instance->getOperand(companion),
                             instance)))
            return WalkResult::interrupt();
        }
        return WalkResult::advance();
      });
      if (result.wasInterrupted())
        return failure();
    }
    return failure(invalid);
  }
};
// Called only after verifyTransactionReturns authenticates the complete graph.
static SmallVector<uint64_t> transactionReturnCompanions(Operation *module) {
  SmallVector<uint64_t> result;
  if (auto metadata = module->getAttrOfType<DictionaryAttr>("ac.transaction_returns"))
    for (Attribute raw : metadata.getAs<ArrayAttr>("incoming"))
      result.push_back(cast<DictionaryAttr>(raw).getAs<IntegerAttr>("enable").getInt());
  return result;
}

// Only companion destinations and required availability operands authorize
// transport of a private fire. Shared ordinary-data consumers invalidate it.
class AvailabilityUses {
  const HardwareAnalysis &analysis;
  DenseSet<OpOperand *> roots, backward;
  DenseMap<OpOperand *, bool> closed;
  DenseSet<OpOperand *> active;
  SmallVector<OpOperand *> pending;
  void add(OpOperand &use, bool root = false) {
    if (root)
      roots.insert(&use);
    if (backward.insert(&use).second)
      pending.push_back(&use);
  }
  bool constantCompanionRead(TableGetOp get) {
    // This is the exact scalar transport emitted when selecting one row of a
    // Boolean companion. The index and membership result are never private
    // availability transports, and a dynamic index must not acquire one here.
    if (!get->getResult(1).use_empty()) return false;
    auto table = dyn_cast<TableType>(get.getInput().getType());
    auto bit = table ? dyn_cast<BitsType>(table.getElementType()) : BitsType();
    auto index = get.getIndex().getDefiningOp<BitsConstantOp>();
    auto indexType = dyn_cast<BitsType>(get.getIndex().getType());
    if (!bit || !index || !indexType ||
        !analysis.isStaticEvaluable(bit.getWidth(), {}) ||
        !analysis.isStaticEvaluable(indexType.getWidth(), {}) ||
        !analysis.isStaticEvaluable(table.getShape(), {})) return false;
    auto literal = index.getValue().getTree().getAs<DictionaryAttr>("value");
    auto integer = literal ? literal.getAs<MathIntAttr>("value") : MathIntAttr();
    uint64_t ordinal;
    if (!integer || integer.getCanonicalValue().getAsInteger(10, ordinal))
      return false;
    auto width = analysis.getPackedWidth(bit, {}, get);
    auto indexWidth = analysis.getPackedWidth(indexType, {}, get);
    auto size = analysis.getTableSize(table, {}, get);
    if (failed(width) || failed(indexWidth) || failed(size) || !*size ||
        *width != 1 || ordinal >= *size ||
        get->getResult(0).getType() != bit ||
        get->getResult(1).getType() != bit) return false;
    uint64_t expectedWidth =
        std::max<uint64_t>(1, llvm::APInt(64, *size - 1).getActiveBits());
    return *indexWidth == expectedWidth;
  }
  bool allUsers(Value value) {
    return llvm::all_of(value.getUses(),
                        [&](OpOperand &use) { return permits(use); });
  }
  bool permits(OpOperand &use) {
    if (roots.contains(&use))
      return true;
    if (!backward.contains(&use)) {
      auto *owner = use.getOwner();
      // A retained, dead availability select/AND has no consumer to expose
      // the control to. This does not authorize an ordinary live data route.
      bool transfer = isa<BitsSelectOp>(owner);
      if (auto binary = dyn_cast<BitsBinaryOp>(owner))
        transfer |= binary.getOpcode() == "and";
      return transfer && llvm::all_of(owner->getResults(), [](Value value) {
               return value.use_empty();
             });
    }
    if (auto known = closed.find(&use); known != closed.end())
      return known->second;
    if (!active.insert(&use).second)
      return false;
    llvm::scope_exit cleanup([&] { active.erase(&use); });
    Operation *owner = use.getOwner();
    bool allowed = false;
    if (auto rule = dyn_cast<RuleOp>(owner))
      allowed =
          allUsers(rule.getBody().front().getArgument(use.getOperandNumber()));
    else if (auto yield = dyn_cast<YieldOp>(owner)) {
      if (auto rule = dyn_cast<RuleOp>(yield->getParentOp()))
        allowed = allUsers(rule->getResult(use.getOperandNumber()));
      else if (auto map = dyn_cast<TableMapOp>(yield->getParentOp()))
        allowed = allUsers(map->getResult(use.getOperandNumber()));
    } else if (auto map = dyn_cast<TableMapOp>(owner)) {
      allowed = allUsers(map.getBody().front().getArgument(use.getOperandNumber() + 1));
    } else if (auto get = dyn_cast<TableGetOp>(owner))
      allowed = use.getOperandNumber() == 0 && constantCompanionRead(get) &&
                allUsers(get->getResult(0));
    else if (isa<BitsBinaryOp, BitsSelectOp, TableCreateOp, TableSplatOp,
                   TableViewOp>(owner))
      allowed = llvm::all_of(owner->getResults(),
                             [&](Value value) { return allUsers(value); });
    else if (auto fold = dyn_cast<TableFoldOp>(owner))
      allowed = fold.getKind() == "and" && allUsers(fold.getResult());
    closed.try_emplace(&use, allowed);
    return allowed;
  }

public:
  explicit AvailabilityUses(const HardwareAnalysis &analysis)
      : analysis(analysis) {}
  FailureOr<DenseSet<OpOperand *>> collect() {
    for (auto module : analysis.getDefinitions()) {
      auto layout = getModulePortLayout(module);
      if (failed(layout))
        return failure();
      auto yield = cast<YieldOp>(module.getBody().front().back());
      for (int64_t companion : layout->outputValidity)
        if (companion >= 0)
          add(yield->getOpOperand(companion), true);
      for (auto [payload, companion] : layout->routedOutputValidity)
        add(yield->getOpOperand(companion), true);
      auto walked = module.walk([&](Operation *operation) {
        if (auto require = dyn_cast<ValueRequireOp>(operation))
          add(require->getOpOperand(1), true);
        if (auto instance = dyn_cast<InstanceOp>(operation)) {
          auto *callee = analysis.resolveCallee(instance);
          if (!callee)
            return WalkResult::interrupt();
          auto ports = getModulePortLayout(callee);
          if (failed(ports))
            return WalkResult::interrupt();
          for (int64_t companion : ports->inputValidity)
            if (companion >= 0)
              add(instance->getOpOperand(companion), true);
          for (uint64_t companion : transactionReturnCompanions(callee))
            add(instance->getOpOperand(companion), true);
        }
        return WalkResult::advance();
      });
      if (walked.wasInterrupted())
        return failure();
    }
    while (!pending.empty()) {
      Value value = pending.pop_back_val()->get();
      if (auto argument = dyn_cast<BlockArgument>(value)) {
        if (auto rule = dyn_cast<RuleOp>(argument.getOwner()->getParentOp()))
          add(rule->getOpOperand(argument.getArgNumber()));
        else if (auto map = dyn_cast<TableMapOp>(argument.getOwner()->getParentOp())) {
          if (argument.getArgNumber()) add(map->getOpOperand(argument.getArgNumber() - 1));
        }
        continue;
      }
      Operation *producer = value.getDefiningOp();
      if (auto op = dyn_cast<BitsBinaryOp>(producer);
          op && op.getOpcode() == "and") {
        add(op->getOpOperand(0));
        add(op->getOpOperand(1));
      } else if (auto op = dyn_cast<BitsSelectOp>(producer)) {
        // The selector is a raw predicate reference, not an availability route.
        add(op->getOpOperand(1));
        add(op->getOpOperand(2));
      } else if (auto get = dyn_cast<TableGetOp>(producer);
                 get && value == get->getResult(0) && constantCompanionRead(get)) {
        add(get->getOpOperand(0));
      } else if (auto fold = dyn_cast<TableFoldOp>(producer); fold && fold.getKind() == "and") {
        add(fold->getOpOperand(0));
      } else if (auto map = dyn_cast<TableMapOp>(producer)) {
        add(map.getBody().front().getTerminator()->getOpOperand(cast<OpResult>(value).getResultNumber()));
      } else if (isa<TableSplatOp, TableViewOp, TableCreateOp>(producer)) {
        for (OpOperand &operand : producer->getOpOperands()) add(operand);
      } else if (auto rule = dyn_cast<RuleOp>(producer)) {
        auto sampled =
            rule->getAttrOfType<DictionaryAttr>("ac.sampled_admission");
        auto fire =
            sampled ? sampled.getAs<IntegerAttr>("fire_result") : IntegerAttr();
        unsigned index = cast<OpResult>(value).getResultNumber();
        if (!fire || fire.getInt() != index)
          add(rule.getBody().front().back().getOpOperand(index));
      }
    }
    DenseSet<OpOperand *> result;
    for (OpOperand *use : backward)
      if (permits(*use))
        result.insert(use);
    // A physical companion cannot be repurposed as public payload or a raw
    // branch predicate inside another definition.
    for (auto module : analysis.getDefinitions()) {
      auto layout = getModulePortLayout(module);
      if (failed(layout))
        return failure();
      for (int64_t companion : layout->inputValidity)
        if (companion >= 0 &&
            !allUsers(module.getBody().front().getArgument(companion)))
          return module.emitOpError()
                 << "availability companion has a data use";
      for (uint64_t companion : transactionReturnCompanions(module))
        if (!allUsers(module.getBody().front().getArgument(companion)))
          return module.emitOpError()
                 << "transaction return availability has a data use";
      auto walked = module.walk([&](InstanceOp instance) {
        auto *callee = analysis.resolveCallee(instance);
        if (!callee)
          return WalkResult::interrupt();
        auto ports = getModulePortLayout(callee);
        if (failed(ports))
          return WalkResult::interrupt();
        for (int64_t companion : ports->outputValidity)
          if (companion >= 0 && !allUsers(instance->getResult(companion))) {
            instance.emitOpError() << "availability companion has a data use";
            return WalkResult::interrupt();
          }
        for (auto [payload, companion] : ports->routedOutputValidity)
          if (!allUsers(instance->getResult(companion))) {
            instance.emitOpError()
                << "routed availability companion has a data use";
            return WalkResult::interrupt();
          }
        return WalkResult::advance();
      });
      if (walked.wasInterrupted())
        return failure();
    }
    return result;
  }
};
bool hasAvailabilityTransport(const HardwareAnalysis &analysis) {
  bool found = false;
  analysis.getPackage().walk([&](Operation *operation) {
    auto sampled =
        operation->getAttrOfType<DictionaryAttr>("ac.sampled_admission");
    found |= isa<ValueRequireOp>(operation) ||
             operation->hasAttr("ac.external_contract") ||
             operation->hasAttr("ac.input_validity") ||
             operation->hasAttr("ac.output_validity") ||
             operation->hasAttr("ac.routed_output_validity") ||
             operation->hasAttr("ac.transaction_returns") ||
             (sampled && sampled.get("requirements"));
  });
  return found;
}
} // namespace
LogicalResult
verifyHardwareValueAvailability(
    const HardwareAnalysis &analysis,
    const std::function<LogicalResult(uint64_t, Operation *)> &debit) {
  // Transport-free packages retain independently checked legacy totality,
  // including literal predicates routed through ordinary instances.
  if (!hasAvailabilityTransport(analysis))
    return success();
  if (failed(verifyTransactionReturns(analysis, debit)))
    return failure();
  if (failed(AvailabilityProof(analysis, debit).run()))
    return failure();
  return success(succeeded(AvailabilityUses(analysis).collect()));
}
FailureOr<DenseSet<OpOperand *>>
getVerifiedValueAvailabilityUses(const HardwareAnalysis &analysis) {
  if (!hasAvailabilityTransport(analysis))
    return DenseSet<OpOperand *>{};
  if (failed(verifyTransactionReturns(analysis, {})))
    return failure();
  if (failed(AvailabilityProof(analysis).run()))
    return failure();
  return AvailabilityUses(analysis).collect();
}
} // namespace acir::ac::detail
