module OwnerLease.Mixed
#lang-pulse
open Pulse.Lib.Pervasives
module C = Class_CellOwner
module L = OwnerLease

#set-options "--z3rlimit 5"

[@@pulse_intro]
ghost fn restore_opened (owner: C.class_CellOwner)
    (value: C.class_CellOwner__model) (p: perm)
  requires L.opened owner value p
  ensures C.class_CellOwner__inv owner #p value
{
  L.end_read owner value p;
  unfold (L.inv owner value p);
}

ghost fn borrowed_call (owner: C.class_CellOwner)
    (#value: erased C.class_CellOwner__model) (#p: perm)
  requires C.class_CellOwner__inv owner #p value
  ensures C.class_CellOwner__inv owner #p value
{}

// The closed q-fraction must not be chosen merely because its pointer matches.
// A valid p-fraction is available through the checked restoration rule instead.
// Pointer-only matching wrongly selects q, then fails to establish q == p.
ghost fn mixed_fraction_valid_call (owner: C.class_CellOwner)
    (value: C.class_CellOwner__model) (p q: perm)
  requires C.class_CellOwner__inv owner #q value **
    L.opened owner value p ** pure (~(p == q))
  ensures C.class_CellOwner__inv owner #q value **
    C.class_CellOwner__inv owner #p value
{
  borrowed_call owner #(hide value) #p;
}
