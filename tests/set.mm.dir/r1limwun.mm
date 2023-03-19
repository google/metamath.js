include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "cr1.mm"
include "cfv.mm"
include "wtr.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "w3a.mm"
include "cwun.mm"
include "r1tr.mm"
include "a1i.mm"
include "cdm.mm"
include "wss.mm"
include "con0.mm"
include "limelon.mm"
include "wfn.mm"
include "wceq.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "syl6eleqr.mm"
include "onssr1.mm"
include "syl.mm"
include "0ellim.mm"
include "adantl.mm"
include "sseldd.mm"
include "ne0i.mm"
include "crnk.mm"
include "rankuni.mm"
include "word.mm"
include "rankon.mm"
include "eloni.mm"
include "orduniss.mm"
include "mp2b.mm"
include "rankr1ai.mm"
include "wi.mm"
include "onuni.mm"
include "adantr.mm"
include "ontr2.mm"
include "sylancr.mm"
include "mp2and.mm"
include "syl5eqel.mm"
include "cima.mm"
include "wb.mm"
include "r1elwf.mm"
include "uniwf.mm"
include "sylib.mm"
include "rankr1ag.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "r1pwcl.mm"
include "biimpa.mm"
include "cun.mm"
include "csuc.mm"
include "ad2antlr.mm"
include "rankprb.mm"
include "limord.mm"
include "ad3antlr.mm"
include "ordunel.mm"
include "syl3anc.mm"
include "limsuc.mm"
include "mpbid.mm"
include "eqeltrd.mm"
include "prwf.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "cvv.mm"
include "fvex.mm"
include "iswun.mm"
include "syl3anbrc.mm"

theorem r1limwun
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ Lim A ) -> ( R1 ` A ) e. WUni )

  proof
    cA
    cV
    wcel
    #
    cA
    wlim
    #
    wa
    #
    cA
    cr1
    cfv
    #
    wtr
    #
    @3
    c0
    wne
    #
    vx
    cv
    #
    cuni
    #
    @3
    wcel
    #
    @6
    cpw
    @3
    wcel
    #
    @6
    vy
    cv
    #
    cpr
    #
    @3
    wcel
    #
    vy
    @3
    wral
    #
    w3a
    #
    vx
    @3
    wral
    #
    @3
    cwun
    wcel
    #
    @4
    @2
    cA
    r1tr
    a1i
    @2
    c0
    @3
    wcel
    @5
    @2
    cA
    @3
    c0
    @2
    cA
    cr1
    cdm
    #
    wcel
    #
    cA
    @3
    wss
    @2
    cA
    con0
    @17
    cA
    cV
    limelon
    #
    cr1
    con0
    wfn
    @17
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    syl6eleqr
    #
    cA
    onssr1
    syl
    @1
    c0
    cA
    wcel
    @0
    cA
    0ellim
    adantl
    sseldd
    @3
    c0
    ne0i
    syl
    @2
    @14
    vx
    @3
    @2
    @6
    @3
    wcel
    #
    wa
    #
    @8
    @9
    @13
    @22
    @8
    @7
    crnk
    cfv
    #
    cA
    wcel
    #
    @22
    @23
    @6
    crnk
    cfv
    #
    cuni
    #
    cA
    @6
    rankuni
    @22
    @26
    @25
    wss
    #
    @25
    cA
    wcel
    #
    @26
    cA
    wcel
    #
    @27
    @22
    @25
    con0
    wcel
    #
    @25
    word
    @27
    @6
    rankon
    #
    @25
    eloni
    @25
    orduniss
    mp2b
    a1i
    @21
    @28
    @2
    @6
    cA
    rankr1ai
    adantl
    #
    @22
    @26
    con0
    wcel
    #
    cA
    con0
    wcel
    #
    @27
    @28
    wa
    @29
    wi
    @30
    @33
    @31
    @25
    onuni
    ax-mp
    @2
    @34
    @21
    @19
    adantr
    @26
    @25
    cA
    ontr2
    sylancr
    mp2and
    syl5eqel
    @22
    @7
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    @18
    @8
    @24
    wb
    @22
    @6
    @35
    wcel
    #
    @36
    @21
    @37
    @2
    @6
    cA
    r1elwf
    #
    adantl
    @6
    uniwf
    sylib
    @2
    @18
    @21
    @20
    adantr
    #
    @7
    cA
    rankr1ag
    syl2anc
    mpbird
    @2
    @21
    @9
    @1
    @21
    @9
    wb
    @0
    @6
    cA
    r1pwcl
    adantl
    biimpa
    @22
    @12
    vy
    @3
    @22
    @10
    @3
    wcel
    #
    wa
    #
    @12
    @11
    crnk
    cfv
    #
    cA
    wcel
    #
    @41
    @42
    @25
    @10
    crnk
    cfv
    #
    cun
    #
    csuc
    #
    cA
    @41
    @37
    @10
    @35
    wcel
    #
    @42
    @46
    wceq
    @21
    @37
    @2
    @40
    @38
    ad2antlr
    #
    @40
    @47
    @22
    @10
    cA
    r1elwf
    adantl
    #
    @6
    @10
    rankprb
    syl2anc
    @41
    @45
    cA
    wcel
    #
    @46
    cA
    wcel
    #
    @41
    cA
    word
    #
    @28
    @44
    cA
    wcel
    #
    @50
    @1
    @52
    @0
    @21
    @40
    cA
    limord
    ad3antlr
    @22
    @28
    @40
    @32
    adantr
    @40
    @53
    @22
    @10
    cA
    rankr1ai
    adantl
    cA
    @25
    @44
    ordunel
    syl3anc
    @1
    @50
    @51
    wb
    @0
    @21
    @40
    cA
    @45
    limsuc
    ad3antlr
    mpbid
    eqeltrd
    @41
    @11
    @35
    wcel
    #
    @18
    @12
    @43
    wb
    @41
    @37
    @47
    @54
    @48
    @49
    @6
    @10
    prwf
    syl2anc
    @22
    @18
    @40
    @39
    adantr
    @11
    cA
    rankr1ag
    syl2anc
    mpbird
    ralrimiva
    3jca
    ralrimiva
    @3
    cvv
    wcel
    @16
    @4
    @5
    @15
    w3a
    wb
    cA
    cr1
    fvex
    vx
    vy
    @3
    cvv
    iswun
    ax-mp
    syl3anbrc
end
