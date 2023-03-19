include "cv.mm"
include "wfn.mm"
include "wsbc.mm"
include "vex.mm"
include "fneq1.mm"
include "sbcie.mm"
include "sbcbii.mm"
include "sbcco.mm"
include "3bitr3i.mm"

theorem bnj62
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint y z
  assert |- ( [. z / x ]. x Fn A <-> z Fn A )

  proof
    vx
    cv
    #
    cA
    wfn
    #
    vx
    vy
    cv
    #
    wsbc
    #
    vy
    vz
    cv
    #
    wsbc
    @2
    cA
    wfn
    #
    vy
    @4
    wsbc
    @1
    vx
    @4
    wsbc
    @4
    cA
    wfn
    #
    @3
    @5
    vy
    @4
    @1
    @5
    vx
    @2
    vy
    vex
    cA
    @0
    @2
    fneq1
    sbcie
    sbcbii
    @1
    vx
    vy
    @4
    sbcco
    @5
    @6
    vy
    @4
    vz
    vex
    cA
    @2
    @4
    fneq1
    sbcie
    3bitr3i
end
