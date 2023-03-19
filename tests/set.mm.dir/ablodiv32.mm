include "cablo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "ablocom.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "ablodivdiv4.mm"
include "3ancomb.mm"
include "sylan2b.mm"
include "3eqtr4d.mm"

theorem ablodiv32
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let cX: class X
  assume abldiv.1: |- X = ran G
  assume abldiv.3: |- D = ( /g ` G )


  assert |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A D B ) D C ) = ( ( A D C ) D B ) )

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
    cG
    co
    #
    cD
    co
    cA
    cC
    cB
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
    cC
    cD
    co
    cA
    cC
    cD
    co
    cB
    cD
    co
    #
    @5
    @6
    @7
    cA
    cD
    @0
    @2
    @3
    @6
    @7
    wceq
    @1
    cB
    cC
    cG
    cX
    abldiv.1
    ablocom
    3adant3r1
    oveq2d
    cA
    cB
    cC
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    ablodivdiv4
    @4
    @0
    @1
    @3
    @2
    w3a
    @9
    @8
    wceq
    @1
    @2
    @3
    3ancomb
    cA
    cC
    cB
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    ablodivdiv4
    sylan2b
    3eqtr4d
end
