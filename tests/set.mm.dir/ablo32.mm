include "cablo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "ablocom.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "cgr.mm"
include "ablogrpo.mm"
include "grpoass.mm"
include "sylan.mm"
include "3ancomb.mm"
include "sylan2b.mm"
include "3eqtr4d.mm"

theorem ablo32
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume ablcom.1: |- X = ran G


  assert |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) G C ) = ( ( A G C ) G B ) )

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
    cG
    co
    #
    cA
    cC
    cB
    cG
    co
    #
    cG
    co
    #
    cA
    cB
    cG
    co
    cC
    cG
    co
    #
    cA
    cC
    cG
    co
    cB
    cG
    co
    #
    @5
    @6
    @8
    cA
    cG
    @0
    @2
    @3
    @6
    @8
    wceq
    @1
    cB
    cC
    cG
    cX
    ablcom.1
    ablocom
    3adant3r1
    oveq2d
    @0
    cG
    cgr
    wcel
    #
    @4
    @10
    @7
    wceq
    cG
    ablogrpo
    #
    cA
    cB
    cC
    cG
    cX
    ablcom.1
    grpoass
    sylan
    @0
    @12
    @4
    @11
    @9
    wceq
    #
    @13
    @4
    @12
    @1
    @3
    @2
    w3a
    @14
    @1
    @2
    @3
    3ancomb
    cA
    cC
    cB
    cG
    cX
    ablcom.1
    grpoass
    sylan2b
    sylan
    3eqtr4d
end
