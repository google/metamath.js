include "wcel.mm"
include "cv.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cuni.mm"
include "wa.mm"
include "wss.mm"
include "wn.mm"
include "con0.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "cardon.mm"
include "eleq1.mm"
include "mpbii.mm"
include "syl6com.mm"
include "ssrdv.mm"
include "ssonuni.mm"
include "syl5.mm"
include "imp.mm"
include "cardonle.mm"
include "syl.mm"
include "onirri.mm"
include "wi.mm"
include "wex.mm"
include "eluni.mm"
include "cdom.mm"
include "wbr.mm"
include "elssuni.mm"
include "ssdomg.mm"
include "adantl.mm"
include "cdm.mm"
include "wb.mm"
include "onenon.mm"
include "ax-mp.mm"
include "syl6eqelr.mm"
include "carddom2.mm"
include "syl2an.mm"
include "sylibrd.mm"
include "sseq1.mm"
include "adantr.mm"
include "sylibd.mm"
include "ssel.mm"
include "syl6.mm"
include "ex.mm"
include "com3r.mm"
include "syld.mm"
include "com4r.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "com13.mm"
include "sylancom.mm"
include "mtoi.mm"
include "word.mm"
include "onordi.mm"
include "eloni.mm"
include "ordtri4.mm"
include "sylancr.mm"
include "mpbir2and.mm"

theorem carduni
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. V -> ( A. x e. A ( card ` x ) = x -> ( card ` U. A ) = U. A ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    #
    ccrd
    cfv
    #
    @1
    wceq
    #
    vx
    cA
    wral
    #
    cA
    cuni
    #
    ccrd
    cfv
    #
    @5
    wceq
    #
    @0
    @4
    wa
    #
    @7
    @6
    @5
    wss
    #
    @6
    @5
    wcel
    #
    wn
    #
    @8
    @5
    con0
    wcel
    #
    @9
    @0
    @4
    @12
    @4
    cA
    con0
    wss
    @0
    @12
    @4
    vy
    cA
    con0
    vy
    cv
    #
    cA
    wcel
    #
    @4
    @13
    ccrd
    cfv
    #
    @13
    wceq
    #
    @13
    con0
    wcel
    #
    @3
    @16
    vx
    @13
    cA
    @1
    @13
    wceq
    #
    @2
    @15
    @1
    @13
    @1
    @13
    ccrd
    fveq2
    @18
    id
    eqeq12d
    rspcv
    #
    @16
    @15
    con0
    wcel
    #
    @17
    @13
    cardon
    #
    @15
    @13
    con0
    eleq1
    mpbii
    syl6com
    ssrdv
    cA
    cV
    ssonuni
    syl5
    imp
    #
    @5
    cardonle
    syl
    @8
    @10
    @6
    @6
    wcel
    #
    @6
    @5
    cardon
    #
    onirri
    @0
    @4
    @12
    @10
    @23
    wi
    #
    @22
    @12
    @4
    @25
    @10
    @4
    @12
    @23
    @10
    @6
    @13
    wcel
    #
    @14
    wa
    #
    vy
    wex
    @4
    @12
    @23
    wi
    wi
    #
    vy
    @6
    cA
    eluni
    @27
    @28
    vy
    @26
    @14
    @28
    @14
    @4
    @12
    @26
    @23
    @14
    @4
    @16
    @12
    @26
    @23
    wi
    #
    wi
    @19
    @16
    @12
    @14
    @29
    @16
    @12
    @14
    @29
    wi
    @16
    @12
    wa
    #
    @14
    @13
    @6
    wss
    #
    @29
    @30
    @14
    @15
    @6
    wss
    #
    @31
    @30
    @14
    @13
    @5
    cdom
    wbr
    #
    @32
    @14
    @13
    @5
    wss
    #
    @30
    @33
    @13
    cA
    elssuni
    @12
    @34
    @33
    wi
    @16
    @13
    @5
    con0
    ssdomg
    adantl
    syl5
    @16
    @13
    ccrd
    cdm
    #
    wcel
    @5
    @35
    wcel
    @32
    @33
    wb
    @12
    @16
    @13
    @15
    @35
    @16
    id
    @20
    @15
    @35
    wcel
    @21
    @15
    onenon
    ax-mp
    syl6eqelr
    @5
    onenon
    @13
    @5
    carddom2
    syl2an
    sylibrd
    @16
    @32
    @31
    wb
    @12
    @15
    @13
    @6
    sseq1
    adantr
    sylibd
    @13
    @6
    @6
    ssel
    syl6
    ex
    com3r
    syld
    com4r
    imp
    exlimiv
    sylbi
    com13
    imp
    sylancom
    mtoi
    @8
    @6
    word
    @5
    word
    #
    @7
    @9
    @11
    wa
    wb
    @6
    @24
    onordi
    @8
    @12
    @36
    @22
    @5
    eloni
    syl
    @6
    @5
    ordtri4
    sylancr
    mpbir2and
    ex
end
