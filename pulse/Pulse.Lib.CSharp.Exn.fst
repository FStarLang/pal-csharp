module Pulse.Lib.CSharp.Exn

/// An exception the BCL declares (doc/translation.md R21.7), identified by the full
/// name of its class. Its message and parameter name are not modelled.
exception BclException of string
