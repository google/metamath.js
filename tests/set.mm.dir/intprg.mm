include "cv.mm"
include "cpr.mm"
include "cint.mm"
include "cin.mm"
include "wceq.mm"
include "preq1.mm"
include "inteqd.mm"
include "ineq1.mm"
include "eqeq12d.mm"
include "preq2.mm"
include "ineq2.mm"
include "vex.mm"
include "intpr.mm"
include "vtocl2g.mm"

theorem intprg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> |^| { A , B } = ( A i^i B ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    cint
    #
    @0
    @1
    cin
    #
    wceq
    cA
    @1
    cpr
    #
    cint
    #
    cA
    @1
    cin
    #
    wceq
    cA
    cB
    cpr
    #
    cint
    #
    cA
    cB
    cin
    #
    wceq
    vx
    vy
    cA
    cB
    cV
    cW
    @0
    cA
    wceq
    #
    @3
    @6
    @4
    @7
    @11
    @2
    @5
    @0
    cA
    @1
    preq1
    inteqd
    @0
    cA
    @1
    ineq1
    eqeq12d
    @1
    cB
    wceq
    #
    @6
    @9
    @7
    @10
    @12
    @5
    @8
    @1
    cB
    cA
    preq2
    inteqd
    @1
    cB
    cA
    ineq2
    eqeq12d
    @0
    @1
    vx
    vex
    vy
    vex
    intpr
    vtocl2g
end
