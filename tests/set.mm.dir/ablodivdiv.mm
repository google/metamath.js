include "cablo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cgr.mm"
include "wceq.mm"
include "ablogrpo.mm"
include "grpodivdiv.mm"
include "sylan.mm"
include "3ancomb.mm"
include "grpomuldivass.mm"
include "ablomuldiv.mm"
include "eqtr3d.mm"
include "sylan2b.mm"
include "eqtrd.mm"

theorem ablodivdiv
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let cX: class X
  assume abldiv.1: |- X = ran G
  assume abldiv.3: |- D = ( /g ` G )


  assert |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A D ( B D C ) ) = ( ( A D B ) G C ) )

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
    cA
    cB
    cC
    cD
    co
    cD
    co
    #
    cA
    cC
    cB
    cD
    co
    cG
    co
    #
    cA
    cB
    cD
    co
    cC
    cG
    co
    #
    @0
    cG
    cgr
    wcel
    #
    @4
    @5
    @6
    wceq
    cG
    ablogrpo
    #
    cA
    cB
    cC
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    grpodivdiv
    sylan
    @4
    @0
    @1
    @3
    @2
    w3a
    #
    @6
    @7
    wceq
    @1
    @2
    @3
    3ancomb
    @0
    @10
    wa
    cA
    cC
    cG
    co
    cB
    cD
    co
    #
    @6
    @7
    @0
    @8
    @10
    @11
    @6
    wceq
    @9
    cA
    cC
    cB
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    grpomuldivass
    sylan
    cA
    cC
    cB
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    ablomuldiv
    eqtr3d
    sylan2b
    eqtrd
end
