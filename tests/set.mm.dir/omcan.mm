include "con0.mm"
include "wcel.mm"
include "w3a.mm"
include "c0.mm"
include "wa.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "omordi.mm"
include "ex.mm"
include "ancoms.mm"
include "3adant2.mm"
include "imp.mm"
include "3adant3.mm"
include "orim12d.mm"
include "con3d.mm"
include "wb.mm"
include "word.mm"
include "omcl.mm"
include "eloni.mm"
include "syl.mm"
include "ordtri3.mm"
include "syl2an.mm"
include "3impdi.mm"
include "adantr.mm"
include "3adant1.mm"
include "3imtr4d.mm"
include "oveq2.mm"
include "impbid1.mm"

theorem omcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. On /\ B e. On /\ C e. On ) /\ (/) e. A ) -> ( ( A .o B ) = ( A .o C ) <-> B = C ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    w3a
    #
    c0
    cA
    wcel
    #
    wa
    #
    cA
    cB
    comu
    co
    #
    cA
    cC
    comu
    co
    #
    wceq
    #
    cB
    cC
    wceq
    #
    @5
    @6
    @7
    wcel
    #
    @7
    @6
    wcel
    #
    wo
    #
    wn
    #
    cB
    cC
    wcel
    #
    cC
    cB
    wcel
    #
    wo
    #
    wn
    #
    @8
    @9
    @5
    @16
    @12
    @5
    @14
    @10
    @15
    @11
    @3
    @4
    @14
    @10
    wi
    #
    @0
    @2
    @4
    @18
    wi
    #
    @1
    @2
    @0
    @19
    @2
    @0
    wa
    @4
    @18
    cB
    cC
    cA
    omordi
    ex
    ancoms
    3adant2
    imp
    @3
    @4
    @15
    @11
    wi
    #
    @0
    @1
    @4
    @20
    wi
    #
    @2
    @1
    @0
    @21
    @1
    @0
    wa
    @4
    @20
    cC
    cB
    cA
    omordi
    ex
    ancoms
    3adant3
    imp
    orim12d
    con3d
    @3
    @8
    @13
    wb
    #
    @4
    @0
    @1
    @2
    @22
    @0
    @1
    wa
    #
    @6
    word
    #
    @7
    word
    #
    @22
    @0
    @2
    wa
    #
    @23
    @6
    con0
    wcel
    @24
    cA
    cB
    omcl
    @6
    eloni
    syl
    @26
    @7
    con0
    wcel
    @25
    cA
    cC
    omcl
    @7
    eloni
    syl
    @6
    @7
    ordtri3
    syl2an
    3impdi
    adantr
    @3
    @9
    @17
    wb
    #
    @4
    @1
    @2
    @27
    @0
    @1
    cB
    word
    cC
    word
    @27
    @2
    cB
    eloni
    cC
    eloni
    cB
    cC
    ordtri3
    syl2an
    3adant1
    adantr
    3imtr4d
    cB
    cC
    cA
    comu
    oveq2
    impbid1
end
