include "cgr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cgn.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr1.mm"
include "grpodivcl.mm"
include "3adant3r1.mm"
include "eqid.mm"
include "grpodivval.mm"
include "syl3anc.mm"
include "grpoinvdiv.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem grpodivdiv
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


  assert |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A D ( B D C ) ) = ( A G ( C D B ) ) )

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
    cC
    cD
    co
    #
    cD
    co
    #
    cA
    @6
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
    cC
    cB
    cD
    co
    #
    cG
    co
    @5
    @0
    @1
    @6
    cX
    wcel
    #
    @7
    @10
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    @0
    @2
    @3
    @12
    @1
    cB
    cC
    cD
    cG
    cX
    grpdivf.1
    grpdivf.3
    grpodivcl
    3adant3r1
    cA
    @6
    cD
    cG
    @8
    cX
    grpdivf.1
    @8
    eqid
    #
    grpdivf.3
    grpodivval
    syl3anc
    @5
    @9
    @11
    cA
    cG
    @0
    @2
    @3
    @9
    @11
    wceq
    @1
    cB
    cC
    cD
    cG
    @8
    cX
    grpdivf.1
    @13
    grpdivf.3
    grpoinvdiv
    3adant3r1
    oveq2d
    eqtrd
end
