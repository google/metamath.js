include "con0.mm"
include "c2o.mm"
include "cdif.mm"
include "wcel.mm"
include "w3a.mm"
include "coe.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "oeordi.mm"
include "ancoms.mm"
include "3adant2.mm"
include "3adant3.mm"
include "orim12d.mm"
include "con3d.mm"
include "wb.mm"
include "eldifi.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "oecl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "word.mm"
include "eloni.mm"
include "ordtri3.mm"
include "syl2an.mm"
include "3adant1.mm"
include "3imtr4d.mm"
include "oveq2.mm"
include "impbid1.mm"

theorem oecan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ( On \ 2o ) /\ B e. On /\ C e. On ) -> ( ( A ^o B ) = ( A ^o C ) <-> B = C ) )

  proof
    cA
    con0
    c2o
    cdif
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
    cA
    cB
    coe
    co
    #
    cA
    cC
    coe
    co
    #
    wceq
    #
    cB
    cC
    wceq
    #
    @3
    @4
    @5
    wcel
    #
    @5
    @4
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
    @6
    @7
    @3
    @14
    @10
    @3
    @12
    @8
    @13
    @9
    @0
    @2
    @12
    @8
    wi
    #
    @1
    @2
    @0
    @16
    cB
    cC
    cA
    oeordi
    ancoms
    3adant2
    @0
    @1
    @13
    @9
    wi
    #
    @2
    @1
    @0
    @17
    cC
    cB
    cA
    oeordi
    ancoms
    3adant3
    orim12d
    con3d
    @3
    @4
    con0
    wcel
    #
    @5
    con0
    wcel
    #
    @6
    @11
    wb
    #
    @3
    cA
    con0
    wcel
    #
    @1
    @18
    @0
    @1
    @21
    @2
    cA
    con0
    c2o
    eldifi
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    cA
    cB
    oecl
    syl2anc
    @3
    @21
    @2
    @19
    @22
    @0
    @1
    @2
    simp3
    cA
    cC
    oecl
    syl2anc
    @18
    @4
    word
    @5
    word
    @20
    @19
    @4
    eloni
    @5
    eloni
    @4
    @5
    ordtri3
    syl2an
    syl2anc
    @1
    @2
    @7
    @15
    wb
    #
    @0
    @1
    cB
    word
    cC
    word
    @23
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
    3imtr4d
    cB
    cC
    cA
    coe
    oveq2
    impbid1
end
