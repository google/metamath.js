include "cablo.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprrl.mm"
include "3jca.mm"
include "ablo32.mm"
include "syldan.mm"
include "oveq1d.mm"
include "cgr.mm"
include "ablogrpo.mm"
include "grpocl.mm"
include "3expb.mm"
include "adantrr.mm"
include "simprrr.mm"
include "grpoass.mm"
include "sylan.mm"
include "adantrlr.mm"
include "adantrrr.mm"
include "3eqtr3d.mm"
include "3impb.mm"

theorem ablo4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume ablcom.1: |- X = ran G


  assert |- ( ( G e. AbelOp /\ ( A e. X /\ B e. X ) /\ ( C e. X /\ D e. X ) ) -> ( ( A G B ) G ( C G D ) ) = ( ( A G C ) G ( B G D ) ) )

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
    wa
    #
    cC
    cX
    wcel
    #
    cD
    cX
    wcel
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
    cG
    co
    cG
    co
    #
    cA
    cC
    cG
    co
    #
    cB
    cD
    cG
    co
    cG
    co
    #
    wceq
    @0
    @3
    @6
    wa
    #
    wa
    #
    @7
    cC
    cG
    co
    #
    cD
    cG
    co
    #
    @9
    cB
    cG
    co
    #
    cD
    cG
    co
    #
    @8
    @10
    @12
    @13
    @15
    cD
    cG
    @0
    @11
    @1
    @2
    @4
    w3a
    @13
    @15
    wceq
    @12
    @1
    @2
    @4
    @0
    @1
    @2
    @6
    simprll
    @0
    @1
    @2
    @6
    simprlr
    @0
    @3
    @4
    @5
    simprrl
    3jca
    cA
    cB
    cC
    cG
    cX
    ablcom.1
    ablo32
    syldan
    oveq1d
    @0
    cG
    cgr
    wcel
    #
    @11
    @14
    @8
    wceq
    #
    cG
    ablogrpo
    #
    @17
    @11
    @7
    cX
    wcel
    #
    @4
    @5
    w3a
    @18
    @17
    @11
    wa
    #
    @20
    @4
    @5
    @17
    @3
    @20
    @6
    @17
    @1
    @2
    @20
    cA
    cB
    cG
    cX
    ablcom.1
    grpocl
    3expb
    adantrr
    @17
    @3
    @4
    @5
    simprrl
    @17
    @3
    @4
    @5
    simprrr
    #
    3jca
    @7
    cC
    cD
    cG
    cX
    ablcom.1
    grpoass
    syldan
    sylan
    @0
    @17
    @11
    @16
    @10
    wceq
    #
    @19
    @17
    @11
    @9
    cX
    wcel
    #
    @2
    @5
    w3a
    @23
    @21
    @24
    @2
    @5
    @17
    @3
    @4
    @24
    @5
    @17
    @1
    @4
    @24
    @2
    @17
    @1
    @4
    @24
    cA
    cC
    cG
    cX
    ablcom.1
    grpocl
    3expb
    adantrlr
    adantrrr
    @17
    @1
    @2
    @6
    simprlr
    @22
    3jca
    @9
    cB
    cD
    cG
    cX
    ablcom.1
    grpoass
    syldan
    sylan
    3eqtr3d
    3impb
end
