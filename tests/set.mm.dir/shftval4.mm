include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cshi.mm"
include "co.mm"
include "cfv.mm"
include "cmin.mm"
include "caddc.mm"
include "wceq.mm"
include "negcl.mm"
include "shftval.mm"
include "sylan.mm"
include "subneg.mm"
include "ancoms.mm"
include "addcom.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem shftval4
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume shftfval.1: |- F e. _V


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( F shift -u A ) ` B ) = ( F ` ( A + B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cB
    cF
    cA
    cneg
    #
    cshi
    co
    cfv
    #
    cB
    @3
    cmin
    co
    #
    cF
    cfv
    #
    cA
    cB
    caddc
    co
    #
    cF
    cfv
    @0
    @3
    cc
    wcel
    @1
    @4
    @6
    wceq
    cA
    negcl
    @3
    cB
    cF
    shftfval.1
    shftval
    sylan
    @2
    @5
    @7
    cF
    @2
    @5
    cB
    cA
    caddc
    co
    #
    @7
    @1
    @0
    @5
    @8
    wceq
    cB
    cA
    subneg
    ancoms
    cA
    cB
    addcom
    eqtr4d
    fveq2d
    eqtrd
end
