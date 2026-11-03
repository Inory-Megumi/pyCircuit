# Retired Method composition

The public `ac.compose` decorator and its dedicated readiness/composition policy
are removed. Old `ac.compose`, `ac.compose_hold`, `ac.state_composition` and
`ac.peer_admissions` IR metadata are rejected. There is no compatibility mode.

Ordinary Methods retain native ordered candidate updates within their calling
Rule. Independent Rules require actual disjoint writes or proven exclusive
grants. Operation policy belongs in ordinary libraries using the
[native operation interfaces](native-actions.md), with explicit independent
updaters where appropriate. The compiler does not infer policy from names.

The preceding implementation and contract are preserved at
[the prior source identity](https://github.com/Inory-Megumi/pyCircuit/tree/d70fd9b62081984b9c5dae7d098639c0d796d531/docs/extensions/compose.md).
Frozen approval/research records remain historical evidence, not current API.
