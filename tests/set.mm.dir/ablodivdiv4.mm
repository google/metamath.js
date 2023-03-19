include "cablo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cgn.mm"
include "cfv.mm"
include "cgr.mm"
include "wceq.mm"
include "ablogrpo.mm"
include "simpl.mm"
include "grpodivcl.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "eqid.mm"
include "grpodivval.mm"
include "syl3anc.mm"
include "sylan.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simp3.mm"
include "grpoinvcl.mm"
include "syl2an.mm"
include "3jca.mm"
include "ablodivdiv.mm"
include "syldan.mm"
include "grpodivinv.mm"
include "syl3an1.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "3eqtr2d.mm"

theorem ablodivdiv4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let cX: class X
  assume abldiv.1: |- X = ran G
  assume abldiv.3: |- D = ( /g ` G )


  assert |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A D B ) D C ) = ( A D ( B G C ) ) )

  proof
    cG
    cablo
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
    cD
    co
    #
    cC
    cD
    co
    #
    @6
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
    @9
    cD
    co
    #
    cD
    co
    #
    cA
    cB
    cC
    cG
    co
    #
    cD
    co
    @0
    cG
    cgr
    wcel
    #
    @4
    @7
    @10
    wceq
    #
    cG
    ablogrpo
    #
    @14
    @4
    wa
    @14
    @6
    cX
    wcel
    #
    @3
    @15
    @14
    @4
    simpl
    @14
    @1
    @2
    @17
    @3
    cA
    cB
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    grpodivcl
    3adant3r3
    @14
    @1
    @2
    @3
    simpr3
    @6
    cC
    cD
    cG
    @8
    cX
    abldiv.1
    @8
    eqid
    #
    abldiv.3
    grpodivval
    syl3anc
    sylan
    @0
    @4
    @1
    @2
    @9
    cX
    wcel
    #
    w3a
    @12
    @10
    wceq
    @5
    @1
    @2
    @19
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
    @14
    @3
    @19
    @4
    @16
    @1
    @2
    @3
    simp3
    cC
    cG
    @8
    cX
    abldiv.1
    @18
    grpoinvcl
    syl2an
    3jca
    cA
    cB
    @9
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    ablodivdiv
    syldan
    @5
    @11
    @13
    cA
    cD
    @0
    @2
    @3
    @11
    @13
    wceq
    #
    @1
    @0
    @14
    @2
    @3
    @20
    @16
    cB
    cC
    cD
    cG
    @8
    cX
    abldiv.1
    @18
    abldiv.3
    grpodivinv
    syl3an1
    3adant3r1
    oveq2d
    3eqtr2d
end
