include "cgr.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "grpoinvcl.mm"
include "3adant2.mm"
include "grpodivval.mm"
include "syld3an3.mm"
include "grpo2inv.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem grpodivinv
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


  assert |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( A D ( N ` B ) ) = ( A G B ) )

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
    cN
    cfv
    #
    cD
    co
    #
    cA
    @4
    cN
    cfv
    #
    cG
    co
    #
    cA
    cB
    cG
    co
    @0
    @1
    @2
    @4
    cX
    wcel
    #
    @5
    @7
    wceq
    @0
    @2
    @8
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
    @4
    cD
    cG
    cN
    cX
    grpdiv.1
    grpdiv.2
    grpdiv.3
    grpodivval
    syld3an3
    @3
    @6
    cB
    cA
    cG
    @0
    @2
    @6
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
    oveq2d
    eqtrd
end
