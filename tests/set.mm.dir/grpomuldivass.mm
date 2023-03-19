include "cgr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cgn.mm"
include "cfv.mm"
include "wceq.mm"
include "simpr1.mm"
include "simpr2.mm"
include "eqid.mm"
include "grpoinvcl.mm"
include "3ad2antr3.mm"
include "3jca.mm"
include "grpoass.mm"
include "syldan.mm"
include "simpl.mm"
include "grpocl.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "grpodivval.mm"
include "syl3anc.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem grpomuldivass
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume grpdivf.1: |- X = ran G
  assume grpdivf.3: |- D = ( /g ` G )


  assert |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) D C ) = ( A G ( B D C ) ) )

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
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cG
    co
    #
    cC
    cG
    cgn
    cfv
    #
    cfv
    #
    cG
    co
    #
    cA
    cB
    @8
    cG
    co
    #
    cG
    co
    #
    @6
    cC
    cD
    co
    #
    cA
    cB
    cC
    cD
    co
    #
    cG
    co
    @0
    @4
    @1
    @2
    @8
    cX
    wcel
    #
    w3a
    @9
    @11
    wceq
    @5
    @1
    @2
    @14
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @3
    @14
    @2
    cC
    cG
    @7
    cX
    grpdivf.1
    @7
    eqid
    #
    grpoinvcl
    3ad2antr3
    3jca
    cA
    cB
    @8
    cG
    cX
    grpdivf.1
    grpoass
    syldan
    @5
    @0
    @6
    cX
    wcel
    #
    @3
    @12
    @9
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @16
    @3
    cA
    cB
    cG
    cX
    grpdivf.1
    grpocl
    3adant3r3
    @0
    @1
    @2
    @3
    simpr3
    @6
    cC
    cD
    cG
    @7
    cX
    grpdivf.1
    @15
    grpdivf.3
    grpodivval
    syl3anc
    @5
    @13
    @10
    cA
    cG
    @0
    @2
    @3
    @13
    @10
    wceq
    @1
    cB
    cC
    cD
    cG
    @7
    cX
    grpdivf.1
    @15
    grpdivf.3
    grpodivval
    3adant3r1
    oveq2d
    3eqtr4d
end
