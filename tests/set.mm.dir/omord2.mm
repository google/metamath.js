include "con0.mm"
include "wcel.mm"
include "w3a.mm"
include "c0.mm"
include "wa.mm"
include "comu.mm"
include "co.mm"
include "wi.mm"
include "omordi.mm"
include "3adantl1.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "oveq2.mm"
include "a1i.mm"
include "3adantl2.mm"
include "orim12d.mm"
include "con3d.mm"
include "wb.mm"
include "omcl.mm"
include "word.mm"
include "eloni.mm"
include "ordtri2.mm"
include "syl2an.mm"
include "anandis.mm"
include "ancoms.mm"
include "3impa.mm"
include "adantr.mm"
include "3adant3.mm"
include "3imtr4d.mm"
include "impbid.mm"

theorem omord2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. On /\ B e. On /\ C e. On ) /\ (/) e. C ) -> ( A e. B <-> ( C .o A ) e. ( C .o B ) ) )

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
    cC
    wcel
    #
    wa
    #
    cA
    cB
    wcel
    #
    cC
    cA
    comu
    co
    #
    cC
    cB
    comu
    co
    #
    wcel
    #
    @1
    @2
    @4
    @6
    @9
    wi
    @0
    cA
    cB
    cC
    omordi
    3adantl1
    @5
    @7
    @8
    wceq
    #
    @8
    @7
    wcel
    #
    wo
    #
    wn
    #
    cA
    cB
    wceq
    #
    cB
    cA
    wcel
    #
    wo
    #
    wn
    #
    @9
    @6
    @5
    @16
    @12
    @5
    @14
    @10
    @15
    @11
    @14
    @10
    wi
    @5
    cA
    cB
    cC
    comu
    oveq2
    a1i
    @0
    @2
    @4
    @15
    @11
    wi
    @1
    cB
    cA
    cC
    omordi
    3adantl2
    orim12d
    con3d
    @3
    @9
    @13
    wb
    #
    @4
    @0
    @1
    @2
    @18
    @2
    @0
    @1
    wa
    @18
    @2
    @0
    @1
    @18
    @2
    @0
    wa
    @7
    con0
    wcel
    #
    @8
    con0
    wcel
    #
    @18
    @2
    @1
    wa
    cC
    cA
    omcl
    cC
    cB
    omcl
    @19
    @7
    word
    @8
    word
    @18
    @20
    @7
    eloni
    @8
    eloni
    @7
    @8
    ordtri2
    syl2an
    syl2an
    anandis
    ancoms
    3impa
    adantr
    @3
    @6
    @17
    wb
    #
    @4
    @0
    @1
    @21
    @2
    @0
    cA
    word
    cB
    word
    @21
    @1
    cA
    eloni
    cB
    eloni
    cA
    cB
    ordtri2
    syl2an
    3adant3
    adantr
    3imtr4d
    impbid
end
