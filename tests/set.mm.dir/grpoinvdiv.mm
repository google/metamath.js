include "cgr.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "grpodivval.mm"
include "fveq2d.mm"
include "wceq.mm"
include "grpoinvcl.mm"
include "3adant2.mm"
include "grpoinvop.mm"
include "syld3an3.mm"
include "grpo2inv.mm"
include "oveq1d.mm"
include "3com23.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem grpoinvdiv
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  assume grpdiv.1: |- X = ran G
  assume grpdiv.2: |- N = ( inv ` G )
  assume grpdiv.3: |- D = ( /g ` G )


  assert |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( N ` ( A D B ) ) = ( B D A ) )

  proof
    cG
    cgr
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cD
    co
    #
    cN
    cfv
    cA
    cB
    cN
    cfv
    #
    cG
    co
    #
    cN
    cfv
    #
    @5
    cN
    cfv
    #
    cA
    cN
    cfv
    #
    cG
    co
    #
    cB
    cA
    cD
    co
    #
    @3
    @4
    @6
    cN
    cA
    cB
    cD
    cG
    cN
    cX
    grpdiv.1
    grpdiv.2
    grpdiv.3
    grpodivval
    fveq2d
    @0
    @1
    @2
    @5
    cX
    wcel
    #
    @7
    @10
    wceq
    @0
    @2
    @12
    @1
    cB
    cG
    cN
    cX
    grpdiv.1
    grpdiv.2
    grpoinvcl
    3adant2
    cA
    @5
    cG
    cN
    cX
    grpdiv.1
    grpdiv.2
    grpoinvop
    syld3an3
    @3
    @10
    cB
    @9
    cG
    co
    #
    @11
    @3
    @8
    cB
    @9
    cG
    @0
    @2
    @8
    cB
    wceq
    @1
    cB
    cG
    cN
    cX
    grpdiv.1
    grpdiv.2
    grpo2inv
    3adant2
    oveq1d
    @0
    @2
    @1
    @11
    @13
    wceq
    cB
    cA
    cD
    cG
    cN
    cX
    grpdiv.1
    grpdiv.2
    grpdiv.3
    grpodivval
    3com23
    eqtr4d
    3eqtrd
end
