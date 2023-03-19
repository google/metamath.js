include "cgr.mm"
include "wcel.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmpt2.mm"
include "grpodivfval.mm"
include "oveqd.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "sylan9eq.mm"
include "3impb.mm"

theorem grpodivval
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


  assert |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( A D B ) = ( A G ( N ` B ) ) )

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
    cA
    cB
    cD
    co
    #
    cA
    cB
    cN
    cfv
    #
    cG
    co
    #
    wceq
    @0
    @1
    @2
    wa
    @3
    cA
    cB
    vx
    vy
    cX
    cX
    vx
    cv
    #
    vy
    cv
    #
    cN
    cfv
    #
    cG
    co
    #
    cmpt2
    #
    co
    @5
    @0
    cD
    @10
    cA
    cB
    vx
    vy
    cD
    cG
    cN
    cX
    grpdiv.1
    grpdiv.2
    grpdiv.3
    grpodivfval
    oveqd
    vx
    vy
    cA
    cB
    cX
    cX
    @9
    @5
    @10
    cA
    @8
    cG
    co
    @6
    cA
    @8
    cG
    oveq1
    @7
    cB
    wceq
    @8
    @4
    cA
    cG
    @7
    cB
    cN
    fveq2
    oveq2d
    @10
    eqid
    cA
    @4
    cG
    ovex
    ovmpt2
    sylan9eq
    3impb
end
