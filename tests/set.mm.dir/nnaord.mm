include "com.mm"
include "wcel.mm"
include "w3a.mm"
include "coa.mm"
include "co.mm"
include "wi.mm"
include "nnaordi.mm"
include "3adant1.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "oveq2.mm"
include "a1i.mm"
include "3adant2.mm"
include "orim12d.mm"
include "con3d.mm"
include "word.mm"
include "wa.mm"
include "wb.mm"
include "df-3an.mm"
include "ancom.mm"
include "anandi.mm"
include "3bitri.mm"
include "nnacl.mm"
include "nnord.mm"
include "syl.mm"
include "anim12i.mm"
include "sylbi.mm"
include "ordtri2.mm"
include "3adant3.mm"
include "3imtr4d.mm"
include "impbid.mm"

theorem nnaord
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. _om /\ B e. _om /\ C e. _om ) -> ( A e. B <-> ( C +o A ) e. ( C +o B ) ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    cC
    com
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
    coa
    co
    #
    cC
    cB
    coa
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
    nnaordi
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
    coa
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
    nnaordi
    3adant2
    orim12d
    con3d
    @3
    @5
    word
    #
    @6
    word
    #
    wa
    #
    @7
    @11
    wb
    @3
    @2
    @0
    wa
    #
    @2
    @1
    wa
    #
    wa
    #
    @18
    @3
    @0
    @1
    wa
    #
    @2
    wa
    @2
    @22
    wa
    @21
    @0
    @1
    @2
    df-3an
    @22
    @2
    ancom
    @2
    @0
    @1
    anandi
    3bitri
    @19
    @16
    @20
    @17
    @19
    @5
    com
    wcel
    @16
    cC
    cA
    nnacl
    @5
    nnord
    syl
    @20
    @6
    com
    wcel
    @17
    cC
    cB
    nnacl
    @6
    nnord
    syl
    anim12i
    sylbi
    @5
    @6
    ordtri2
    syl
    @3
    cA
    word
    #
    cB
    word
    #
    wa
    #
    @4
    @15
    wb
    @0
    @1
    @25
    @2
    @0
    @23
    @1
    @24
    cA
    nnord
    cB
    nnord
    anim12i
    3adant3
    cA
    cB
    ordtri2
    syl
    3imtr4d
    impbid
end
