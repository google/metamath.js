include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "hvadd32.mm"
include "oveq1d.mm"
include "3expa.mm"
include "adantrr.mm"
include "hvaddcl.mm"
include "ax-hvass.mm"
include "3expb.mm"
include "sylan.mm"
include "an4s.mm"
include "3eqtr3d.mm"

theorem hvadd4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. ~H /\ B e. ~H ) /\ ( C e. ~H /\ D e. ~H ) ) -> ( ( A +h B ) +h ( C +h D ) ) = ( ( A +h C ) +h ( B +h D ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cC
    chil
    wcel
    #
    cD
    chil
    wcel
    #
    wa
    #
    wa
    cA
    cB
    cva
    co
    #
    cC
    cva
    co
    #
    cD
    cva
    co
    #
    cA
    cC
    cva
    co
    #
    cB
    cva
    co
    #
    cD
    cva
    co
    #
    @6
    cC
    cD
    cva
    co
    cva
    co
    #
    @9
    cB
    cD
    cva
    co
    cva
    co
    #
    @2
    @3
    @8
    @11
    wceq
    #
    @4
    @0
    @1
    @3
    @14
    @0
    @1
    @3
    w3a
    @7
    @10
    cD
    cva
    cA
    cB
    cC
    hvadd32
    oveq1d
    3expa
    adantrr
    @2
    @6
    chil
    wcel
    #
    @5
    @8
    @12
    wceq
    #
    cA
    cB
    hvaddcl
    @15
    @3
    @4
    @16
    @6
    cC
    cD
    ax-hvass
    3expb
    sylan
    @0
    @3
    @1
    @4
    @11
    @13
    wceq
    #
    @0
    @3
    wa
    @9
    chil
    wcel
    #
    @1
    @4
    wa
    @17
    cA
    cC
    hvaddcl
    @18
    @1
    @4
    @17
    @9
    cB
    cD
    ax-hvass
    3expb
    sylan
    an4s
    3eqtr3d
end
