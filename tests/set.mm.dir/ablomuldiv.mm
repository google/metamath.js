include "cablo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "ablocom.mm"
include "3adant3r3.mm"
include "oveq1d.mm"
include "3ancoma.mm"
include "cgr.mm"
include "ablogrpo.mm"
include "grpomuldivass.mm"
include "sylan.mm"
include "sylan2b.mm"
include "simpr2.mm"
include "grpodivcl.mm"
include "syl3an1.mm"
include "3adant3r2.mm"
include "jca.mm"
include "3expb.mm"
include "syldan.mm"
include "3eqtrd.mm"

theorem ablomuldiv
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let cX: class X
  assume abldiv.1: |- X = ran G
  assume abldiv.3: |- D = ( /g ` G )


  assert |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) D C ) = ( ( A D C ) G B ) )

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
    cG
    co
    #
    cC
    cD
    co
    cB
    cA
    cG
    co
    #
    cC
    cD
    co
    #
    cB
    cA
    cC
    cD
    co
    #
    cG
    co
    #
    @9
    cB
    cG
    co
    #
    @5
    @6
    @7
    cC
    cD
    @0
    @1
    @2
    @6
    @7
    wceq
    @3
    cA
    cB
    cG
    cX
    abldiv.1
    ablocom
    3adant3r3
    oveq1d
    @4
    @0
    @2
    @1
    @3
    w3a
    #
    @8
    @10
    wceq
    #
    @1
    @2
    @3
    3ancoma
    @0
    cG
    cgr
    wcel
    #
    @12
    @13
    cG
    ablogrpo
    #
    cB
    cA
    cC
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    grpomuldivass
    sylan
    sylan2b
    @0
    @4
    @2
    @9
    cX
    wcel
    #
    wa
    @10
    @11
    wceq
    #
    @5
    @2
    @16
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @3
    @16
    @2
    @0
    @14
    @1
    @3
    @16
    @15
    cA
    cC
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    grpodivcl
    syl3an1
    3adant3r2
    jca
    @0
    @2
    @16
    @17
    cB
    @9
    cG
    cX
    abldiv.1
    ablocom
    3expb
    syldan
    3eqtrd
end
