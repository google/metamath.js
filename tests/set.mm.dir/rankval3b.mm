include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "cv.mm"
include "wral.mm"
include "crab.mm"
include "cint.mm"
include "wa.mm"
include "cab.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "wb.mm"
include "rankon.mm"
include "simprl.mm"
include "ontri1.mm"
include "sylancr.mm"
include "con2bid.mm"
include "cdm.mm"
include "r1elssi.mm"
include "adantr.mm"
include "sselda.mm"
include "rankdmr1.mm"
include "wlim.mm"
include "word.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ordtr1.mm"
include "mp2b.mm"
include "mpan2.mm"
include "ad2antlr.mm"
include "rankr1ag.mm"
include "syl2anc.mm"
include "ralbidva.mm"
include "biimpar.mm"
include "an32s.mm"
include "dfss3.mm"
include "sylibr.mm"
include "simpll.mm"
include "adantl.mm"
include "rankr1bg.mm"
include "mpbid.mm"
include "ex.mm"
include "adantrl.mm"
include "sylbird.mm"
include "pm2.18d.mm"
include "alrimiv.mm"
include "ssintab.mm"
include "df-rab.mm"
include "inteqi.mm"
include "syl6sseqr.mm"
include "rankelb.mm"
include "ralrimiv.mm"
include "wceq.mm"
include "eleq2.mm"
include "ralbidv.mm"
include "onintss.mm"
include "mpsyl.mm"
include "eqssd.mm"

theorem rankval3b
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A e. U. ( R1 " On ) -> ( rank ` A ) = |^| { x e. On | A. y e. A ( rank ` y ) e. x } )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cA
    crnk
    cfv
    #
    vy
    cv
    #
    crnk
    cfv
    #
    vx
    cv
    #
    wcel
    #
    vy
    cA
    wral
    #
    vx
    con0
    crab
    #
    cint
    #
    @1
    @2
    @5
    con0
    wcel
    #
    @7
    wa
    #
    vx
    cab
    #
    cint
    #
    @9
    @1
    @11
    @2
    @5
    wss
    #
    wi
    #
    vx
    wal
    @2
    @13
    wss
    @1
    @15
    vx
    @1
    @11
    @14
    @1
    @11
    wa
    #
    @14
    @16
    @14
    wn
    @5
    @2
    wcel
    #
    @14
    @16
    @14
    @17
    @16
    @2
    con0
    wcel
    #
    @10
    @14
    @17
    wn
    wb
    cA
    rankon
    #
    @1
    @10
    @7
    simprl
    @2
    @5
    ontri1
    sylancr
    con2bid
    @1
    @7
    @17
    @14
    wi
    @10
    @1
    @7
    wa
    #
    @17
    @14
    @20
    @17
    wa
    #
    cA
    @5
    cr1
    cfv
    #
    wss
    #
    @14
    @21
    @3
    @22
    wcel
    #
    vy
    cA
    wral
    #
    @23
    @1
    @17
    @7
    @25
    @1
    @17
    wa
    #
    @25
    @7
    @26
    @24
    @6
    vy
    cA
    @26
    @3
    cA
    wcel
    #
    wa
    @3
    @0
    wcel
    @5
    cr1
    cdm
    #
    wcel
    #
    @24
    @6
    wb
    @26
    cA
    @0
    @3
    @1
    cA
    @0
    wss
    @17
    cA
    r1elssi
    adantr
    sselda
    @17
    @29
    @1
    @27
    @17
    @2
    @28
    wcel
    #
    @29
    cA
    rankdmr1
    @28
    wlim
    #
    @28
    word
    @17
    @30
    wa
    @29
    wi
    cr1
    wfun
    @31
    r1funlim
    simpri
    @28
    limord
    @5
    @2
    @28
    ordtr1
    mp2b
    mpan2
    #
    ad2antlr
    @3
    @5
    rankr1ag
    syl2anc
    ralbidva
    biimpar
    an32s
    vy
    cA
    @22
    dfss3
    sylibr
    @21
    @1
    @29
    @23
    @14
    wb
    @1
    @7
    @17
    simpll
    @17
    @29
    @20
    @32
    adantl
    cA
    @5
    rankr1bg
    syl2anc
    mpbid
    ex
    adantrl
    sylbird
    pm2.18d
    ex
    alrimiv
    @11
    vx
    @2
    ssintab
    sylibr
    @8
    @12
    @7
    vx
    con0
    df-rab
    inteqi
    syl6sseqr
    @18
    @1
    @4
    @2
    wcel
    #
    vy
    cA
    wral
    #
    @9
    @2
    wss
    @19
    @1
    @33
    vy
    cA
    @3
    cA
    rankelb
    ralrimiv
    @7
    @34
    vx
    @2
    @5
    @2
    wceq
    @6
    @33
    vy
    cA
    @5
    @2
    @4
    eleq2
    ralbidv
    onintss
    mpsyl
    eqssd
end
