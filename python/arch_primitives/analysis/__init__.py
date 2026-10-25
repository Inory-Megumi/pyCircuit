"""Optional host analysis; importing this package does not require NetworkX."""

from .fsm import GraphAnalysisError, analyze_graph, analyze_source, render_text


__all__ = ['GraphAnalysisError', 'analyze_graph', 'analyze_source', 'render_text']
