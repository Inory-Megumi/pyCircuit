# RTL 可读性：官方基线上的移植研究

2026-11-05。当前检查点为 `87ff3b0d9731809a32d33a70a3c6a6d8d4a91fd2`，
已推送到 `Inory-Megumi/pyCircuit` 的 `codex/rule-order-20261105`。
本研究位于本地分支 `codex/rtl-readable-20261105`。
目标是让使用者能从生成 RTL 找回原变量、Rule 和状态更新，保持现有
`schedule(first, second, third)`、单一 `dwire()` 与 C++ 模型语义。

本文保留移植设计与初始基线记录。随后实施的范围、命令与限制见
[Physical RTL 展示层](rtl-presentation.md)，不代表旧 archlab 全部功能移植完成。

## 复用哪些历史成果

| 历史版本 | 值得复用的部分 | 当前移植边界 |
| --- | --- | --- |
| 10 月 30 日，`f46264d10251924587e99647cadf51ea5d5f9641` | 用 Location 保存来源，不制造额外 SSA use；同源 IR/C++ 对照 | 保留方法，不整体合入旧 SDK |
| 11 月 3 日 foundation，`6f142aefb7bd0e55daa87f91180518b1d05b14a0` | 完整实例路径、实际根 Rule 归属、精确常量转发 | 该提交也包含其他前端/合同变更，不能整笔 cherry-pick |
| 11 月 3 日 presentation，`ec6fb5abc61571180f7f09e2a4e3170ab6955ffa` | 类型化展示图、共享表达式、成本约束、统一命名/分区、完整名称映射 | 作为主要设计参考，逐层适配当前 IR |

archlab 的原始记录是 `work/rtl_readability/INTEGRATION_20261030.md`、
`work/native_rtl_readability_20261103/README.md`、
`work/rtl_presentation_20261103/DESIGN.md` 和
`work/rtl_push_20261103/commits.json`。
保留这些历史记录的身份；它们的测试结果不能算作本分支的验证。

主要代码参照来自旧发布快照 `.tools/rtl-push-20261103/source`：

| 旧文件 | 移植用途 |
| --- | --- |
| `compiler/lib/Transforms/TransactionRtlProvenance.inc` | 实际原子根、源位置和用途的确定性传播 |
| `compiler/lib/Compiler/RtlPresentationPlan.h` | 展示图、活跃性、消费者、共享和表达式成本 |
| `compiler/lib/Compiler/HardwareEmitVerilogReadability.inc` | 确切别名、常量与渲染边界 |
| `compiler/lib/Compiler/HardwareEmitVerilogRoles.inc` | 作者绑定优先；多来源归入共享逻辑 |
| `compiler/lib/Compiler/HardwareEmitVerilogSectionPlan.inc` | 声明、Rule 逻辑、共享逻辑和状态提交的布局 |

## 当前版本缺什么

当前 `HardwareEmitVerilogDefinition.cpp` 的 `NetEmitter::net()` 在访问值时
直接分配 `pyc_net_N`。实例结果、普通表达式和 Table 操作分别分配名字，
缺少统一的消费者/来源计划；源码行号存在，但没有逐个 RTL 信号的对应表。

`ac.dwire` 已保留 `instance_name`、`occurrence` 和位置；寄存器实例也保留
作者状态名。因此第一步可以保留 `inc`、`dec`、`count`。但中间条件、
Rule 内部计算和共享子表达式的归属，不能仅靠这些状态名字推测。
当前版本没有旧展示层依赖的 `sourceRtlRoles`/`retainSourceRtlOwner`
一类来源接口，需要在现有 lowering 边界重新接入。

当前 CLI 只有 `managed` 和 `physical` 两种 RTL 模式。旧实现的
`synthesis` 模式不能当作现有功能，也不能拿它的行数与 managed 输出
直接比较，宣称可读性改进。第一轮使用同一 Counter 顶层的 physical 输出。

## 第一轮：一起审阅 DWire 计数器

输入固定为现有 `examples/dwire_counter/dwire_counter.py` 的
`Counter` 顶层；不把 System 日志或场景代码混入展示比较。

| Python 对象/操作 | 展示意图 | 必须保留的关系 |
| --- | --- | --- |
| `count` | 可辨认的当前状态、更新值和更新使能 | 一个真实计数寄存器，初值和复位不变 |
| `inc = dwire()`、`dec = dwire()` | 以作者名字呈现的组合线 | 成功写入发布，否则驱动零，不增加寄存器 |
| `increment`、`decrement` | 分别标明原 Rule 的条件和效果 | 两个独立原子根，不能画成排他的仲裁 |
| `update` | 聚集比较、加减选择与状态更新逻辑 | 同拍加减抵消；读取 DWire 不意味着跨根回滚 |
| 来源映射 | 从 RTL 信号/语句找到文件、行、变量及原 Rule | 完整实例路径；多来源明确表示共享 |

这些是待实现的展示要求，不是已经生成的新 RTL 名称。
源码中的局部绑定可能成为别名，一条 RTL 信号也可能对应多个源码位置；
映射应允许多对多，不能为了逐行对应复制硬件。

建议分三个可审阅的小步：

1. **作者名字和出处**：为状态、DWire 与真正保留的局部值提供统一名字分配；
   复用已有标识符转义，处理端口、关键字、同名局部和实例冲突；
   同时输出名称与来源映射，避免只有好看的名字却没有身份依据。
2. **表达式计划**：对已验证 common IR 建立只读展示图，先统计实际消费者，
   再决定展开或命名。常量必须精确保留位宽和 X/Z；共享生产者保留一份。
   用显式工作栈和缓存，避免逐个信号重复递归整张图。
3. **Rule 与状态布局**：按真实原子根组织逻辑，单列共享逻辑和最终状态提交。
   `schedule` 产生的同拍状态版本需显示先后与最终提交；未参加调度的根
   仍保持独立。显示顺序本身不能暗示新的执行顺序。

不先移植旧接口展开、Table 展示和复杂控制美化；它们在基础计划稳定后
走同一套图和来源接口，不为计数器做文本替换或特殊打印模板。

## 正确性与编译成本要求

展示层只引用已验证、已优化的 common IR，不改变状态更新、准入、检查、
四态运算、DWire 默认零或调度。来源元数据不能新增语义 use 或阻止优化。
未知控制的处理仍依赖原检查；不能把四态表达式当普通二态布尔式约简。

常量/别名追踪停在寄存器、资源与非透明调用边界。合法的字段级依赖不能
因为展示图按整个聚合值计算而被误判为新组合环。

验收分别记录：

- 同源变更前后的 common IR（仅允许展示 Location 差异）、C++ 和 managed
  RTL；物理接口、状态数量、共享运算身份与来源覆盖。
- Counter 的独立行为预期：无请求保持、单独加减、同时请求抵消，且不多一拍。
  多位 DWire 的 X/Z、无写入归零用四态仿真单独检查。
- 重名、同定义多实例、共享表达式和显式调度状态转发，避免展示名误导语义。
- compile/link/emit 分阶段耗时及峰值内存；重复独立进程测量，并记录中位数、
  模型规模与节点/边数。保留现有共享/不同源单元及无修改重建基准。

历史表达式展开阈值可以作为起点，不能通过提高验证预算掩盖展示算法成本。
第一轮不宣称形式等价、PPA 或大型 HNI 的性能结果。

## 本轮已处理的基线问题

使用新顶层建立 physical 基线时发现：`ac.dwire` 的 clock 操作数只是
域身份元数据，却被物理导出检查当作组合数据使用而拒绝。
局部修正验证其 clock/reset 必须是实际根域，再仅允许 clock 的元数据槽位；
enable、data、idle 槽位仍受时钟数据使用检查。没有删除控制或提交检查。

该修正安装在单独的 `install-readable`，此前的 `install-dwire` 与默认 SDK
不变。新增 Counter 的 physical Icarus/Verilator 行为检查，以及多位 DWire
的 Icarus X/Z/归零检查。具体运行结果和字节对照记录放在忽略的
`docs/gates/logs/rtl-readability-baseline-20261105/`；研究设计不能代替这些结果。

上述基线阶段只完成来源梳理与可执行基线，不把当时的 RTL 标记为
“可读性优化后”。后续展示层的实现和资格单独记录，不覆盖该初始证据。
