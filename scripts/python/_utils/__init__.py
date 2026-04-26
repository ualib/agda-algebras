"""
File: scripts/python/_utils/__init__.py

Description:
  Utility modules for functional programming and mathematical pipeline operations.

  This package provides the mathematical foundations for the documentation build pipeline,
  including immutable data structures, functional error handling, and pure transformations.

Provenance:
  Adapted from formalverification/agda-native-air/ at SHA 664b919.  See NOTICE.
"""

from .pipeline_types import (
    # Functional error handling
    Result,
    PipelineError,
    ErrorType,

    # Pipeline state management
    PipelineState,
    PipelineStatistics,
    ProcessedFile,
    FileMetadata,
    ProcessingStage,

    # Command execution
    CommandResult,

    # Function types
    ProcessingFunction,
    FileTransformer,
    PipelineStage,

    # Utility functions
    sequence_results,
    collect_errors,
)

__all__ = [
    # Error handling
    "Result",
    "PipelineError",
    "ErrorType",

    # State management
    "PipelineState",
    "PipelineStatistics",
    "ProcessedFile",
    "FileMetadata",
    "ProcessingStage",

    # Command execution
    "CommandResult",

    # Function types
    "ProcessingFunction",
    "FileTransformer",
    "PipelineStage",

    # Utilities
    "sequence_results",
    "collect_errors",
]
