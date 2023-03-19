include "word.mm"
include "wa.mm"
include "wcel.mm"
include "wceq.mm"
include "w3o.mm"
include "wpss.mm"
include "wss.mm"
include "wo.mm"
include "cin.mm"
include "wn.mm"
include "ordin.mm"
include "ordirr.mm"
include "syl.mm"
include "ianor.mm"
include "elin.mm"
include "incom.mm"
include "eleq1i.mm"
include "anbi2i.mm"
include "bitri.mm"
include "xchnxbir.mm"
include "sylib.mm"
include "inss1.mm"
include "ordsseleq.mm"
include "mpbii.mm"
include "sylan.mm"
include "anabss1.mm"
include "ord.mm"
include "df-ss.mm"
include "syl6ibr.mm"
include "anabss4.mm"
include "orim12d.mm"
include "mpd.mm"
include "sspsstri.mm"
include "ordelpss.mm"
include "biidd.mm"
include "wb.mm"
include "ancoms.mm"
include "3orbi123d.mm"
include "mpbird.mm"

theorem ordtri3or
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A e. B \/ A = B \/ B e. A ) )

  proof
    cA
    word
    #
    cB
    word
    #
    wa
    #
    cA
    cB
    wcel
    #
    cA
    cB
    wceq
    #
    cB
    cA
    wcel
    #
    w3o
    cA
    cB
    wpss
    #
    @4
    cB
    cA
    wpss
    #
    w3o
    #
    @2
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wo
    #
    @8
    @2
    cA
    cB
    cin
    #
    cA
    wcel
    #
    wn
    #
    cB
    cA
    cin
    #
    cB
    wcel
    #
    wn
    #
    wo
    #
    @11
    @2
    @12
    @12
    wcel
    #
    wn
    #
    @18
    @2
    @12
    word
    #
    @20
    cA
    cB
    ordin
    #
    @12
    ordirr
    syl
    @13
    @16
    wa
    #
    @18
    @19
    @13
    @16
    ianor
    @19
    @13
    @12
    cB
    wcel
    #
    wa
    @23
    @12
    cA
    cB
    elin
    @24
    @16
    @13
    @12
    @15
    cB
    cA
    cB
    incom
    eleq1i
    anbi2i
    bitri
    xchnxbir
    sylib
    @2
    @14
    @9
    @17
    @10
    @2
    @14
    @12
    cA
    wceq
    #
    @9
    @2
    @13
    @25
    @0
    @1
    @13
    @25
    wo
    #
    @2
    @21
    @0
    @26
    @22
    @21
    @0
    wa
    @12
    cA
    wss
    @26
    cA
    cB
    inss1
    @12
    cA
    ordsseleq
    mpbii
    sylan
    anabss1
    ord
    cA
    cB
    df-ss
    syl6ibr
    @2
    @17
    @15
    cB
    wceq
    #
    @10
    @2
    @16
    @27
    @0
    @1
    @16
    @27
    wo
    #
    @1
    @0
    wa
    @15
    word
    #
    @1
    @28
    cB
    cA
    ordin
    @29
    @1
    wa
    @15
    cB
    wss
    @28
    cB
    cA
    inss1
    @15
    cB
    ordsseleq
    mpbii
    sylan
    anabss4
    ord
    cB
    cA
    df-ss
    syl6ibr
    orim12d
    mpd
    cA
    cB
    sspsstri
    sylib
    @2
    @3
    @6
    @4
    @4
    @5
    @7
    cA
    cB
    ordelpss
    @2
    @4
    biidd
    @1
    @0
    @5
    @7
    wb
    cB
    cA
    ordelpss
    ancoms
    3orbi123d
    mpbird
end
