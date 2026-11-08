module Pulse.Lib.CSharp.Platform

/// What a program can ask about the platform it runs on (doc/translation.md R33.4).
/// Every `val` here is a MODELING AXIOM.

/// `IntPtr.Size`: the size of a pointer, in bytes. A constant of the process, and nothing
/// more is assumed: in particular not which of 4 or 8 it is, so code that branches on it is
/// verified along both branches.
val intptr_size : FStar.Int32.t
