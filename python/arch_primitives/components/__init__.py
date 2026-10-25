"""Built-in architecture components and their elaboration registrations."""

from .pipe import PIPE_COMPONENT, Pipe, PipeError
from .table import TABLE_COMPONENT, Table, TableError
from .arbiter import ARBITER_COMPONENT, Arbiter, ArbiterError
from .fsm import FSM_COMPONENT, FSM, FSMError, Pattern, Edge, Next


COMPONENTS = (PIPE_COMPONENT, TABLE_COMPONENT, ARBITER_COMPONENT, FSM_COMPONENT)

__all__ = ['Pipe', 'PipeError', 'Table', 'TableError', 'Arbiter', 'ArbiterError', 'FSM', 'FSMError', 'Pattern', 'Edge', 'Next']
