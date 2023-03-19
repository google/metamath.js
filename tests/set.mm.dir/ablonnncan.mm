include "cablo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpr1.mm"
include "cgr.mm"
include "ablogrpo.mm"
include "grpodivcl.mm"
include "syl3an1.mm"
include "3adant3r1.mm"
include "simpr3.mm"
include "3jca.mm"
include "ablodivdiv4.mm"
include "syldan.mm"
include "grponpcan.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem ablonnncan
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let cX: class X
  assume abldiv.1: |- X = ran G
  assume abldiv.3: |- D = ( /g ` G )


  assert |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A D ( B D C ) ) D C ) = ( A D B ) )

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
    cC
    cD
    co
    #
    cD
    co
    cC
    cD
    co
    #
    cA
    @6
    cC
    cG
    co
    #
    cD
    co
    #
    cA
    cB
    cD
    co
    @0
    @4
    @1
    @6
    cX
    wcel
    #
    @3
    w3a
    @7
    @9
    wceq
    @5
    @1
    @10
    @3
    @0
    @1
    @2
    @3
    simpr1
    @0
    @2
    @3
    @10
    @1
    @0
    cG
    cgr
    wcel
    #
    @2
    @3
    @10
    cG
    ablogrpo
    #
    cB
    cC
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    grpodivcl
    syl3an1
    3adant3r1
    @0
    @1
    @2
    @3
    simpr3
    3jca
    cA
    @6
    cC
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    ablodivdiv4
    syldan
    @5
    @8
    cB
    cA
    cD
    @0
    @2
    @3
    @8
    cB
    wceq
    #
    @1
    @0
    @11
    @2
    @3
    @13
    @12
    cB
    cC
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    grponpcan
    syl3an1
    3adant3r1
    oveq2d
    eqtrd
end
