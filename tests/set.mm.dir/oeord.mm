include "con0.mm"
include "wcel.mm"
include "c2o.mm"
include "cdif.mm"
include "w3a.mm"
include "coe.mm"
include "co.mm"
include "wi.mm"
include "oeordi.mm"
include "3adant1.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "oveq2.mm"
include "a1i.mm"
include "3adant2.mm"
include "orim12d.mm"
include "con3d.mm"
include "wb.mm"
include "eldifi.mm"
include "3ad2ant3.mm"
include "simp1.mm"
include "oecl.mm"
include "syl2anc.mm"
include "simp2.mm"
include "word.mm"
include "eloni.mm"
include "ordtri2.mm"
include "syl2an.mm"
include "3adant3.mm"
include "3imtr4d.mm"
include "impbid.mm"

theorem oeord
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. On /\ B e. On /\ C e. ( On \ 2o ) ) -> ( A e. B <-> ( C ^o A ) e. ( C ^o B ) ) )

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
    c2o
    cdif
    wcel
    #
    w3a
    #
    cA
    cB
    wcel
    #
    cC
    cA
    coe
    co
    #
    cC
    cB
    coe
    co
    #
    wcel
    #
    @1
    @2
    @4
    @7
    wi
    @0
    cA
    cB
    cC
    oeordi
    3adant1
    @3
    @5
    @6
    wceq
    #
    @6
    @5
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
    @7
    @4
    @3
    @14
    @10
    @3
    @12
    @8
    @13
    @9
    @12
    @8
    wi
    @3
    cA
    cB
    cC
    coe
    oveq2
    a1i
    @0
    @2
    @13
    @9
    wi
    @1
    cB
    cA
    cC
    oeordi
    3adant2
    orim12d
    con3d
    @3
    @5
    con0
    wcel
    #
    @6
    con0
    wcel
    #
    @7
    @11
    wb
    #
    @3
    cC
    con0
    wcel
    #
    @0
    @16
    @2
    @0
    @19
    @1
    cC
    con0
    c2o
    eldifi
    3ad2ant3
    #
    @0
    @1
    @2
    simp1
    cC
    cA
    oecl
    syl2anc
    @3
    @19
    @1
    @17
    @20
    @0
    @1
    @2
    simp2
    cC
    cB
    oecl
    syl2anc
    @16
    @5
    word
    @6
    word
    @18
    @17
    @5
    eloni
    @6
    eloni
    @5
    @6
    ordtri2
    syl2an
    syl2anc
    @0
    @1
    @4
    @15
    wb
    #
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
    3imtr4d
    impbid
end
