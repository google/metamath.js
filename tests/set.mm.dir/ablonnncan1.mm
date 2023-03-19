include "cablo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpr1.mm"
include "simpr2.mm"
include "cgr.mm"
include "ablogrpo.mm"
include "grpodivcl.mm"
include "syl3an1.mm"
include "3adant3r2.mm"
include "3jca.mm"
include "ablodiv32.mm"
include "syldan.mm"
include "ablonncan.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem ablonnncan1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let cX: class X
  assume abldiv.1: |- X = ran G
  assume abldiv.3: |- D = ( /g ` G )


  assert |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A D B ) D ( A D C ) ) = ( C D B ) )

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
    cA
    cC
    cD
    co
    #
    cD
    co
    #
    cA
    @6
    cD
    co
    #
    cB
    cD
    co
    #
    cC
    cB
    cD
    co
    @0
    @4
    @1
    @2
    @6
    cX
    wcel
    #
    w3a
    @7
    @9
    wceq
    @5
    @1
    @2
    @10
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
    @10
    @2
    @0
    cG
    cgr
    wcel
    @1
    @3
    @10
    cG
    ablogrpo
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
    3jca
    cA
    cB
    @6
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    ablodiv32
    syldan
    @5
    @8
    cC
    cB
    cD
    @0
    @1
    @3
    @8
    cC
    wceq
    @2
    cA
    cC
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    ablonncan
    3adant3r2
    oveq1d
    eqtrd
end
