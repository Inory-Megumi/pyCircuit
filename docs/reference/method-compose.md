# Retired Method composition reference

`ac.compose` is retired. See the [retirement boundary](../extensions/compose.md)
and [native operation interfaces](../extensions/native-actions.md).

Bare Methods keep their ordered transactional semantics. Repeated writes within
one caller are distinct from overlapping independent roots. Removing Compose
neither fuses those roots nor introduces an implicit arbiter or rollback group.
