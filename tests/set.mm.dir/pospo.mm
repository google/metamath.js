include "wcel.mm"
include "cpo.mm"
include "wpo.mm"
include "cid.mm"
include "cres.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "pltirr.mm"
include "plttr.mm"
include "ispod.mm"
include "wrel.mm"
include "relres.mm"
include "a1i.mm"
include "cop.mm"
include "wceq.mm"
include "copab.mm"
include "opabresid.mm"
include "eleq2i.mm"
include "opabid.mm"
include "bitr3i.mm"
include "wbr.mm"
include "posref.mm"
include "df-br.mm"
include "breq2.mm"
include "syl5bbr.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "relssdv.mm"
include "jca.mm"
include "cvv.mm"
include "elex.mm"
include "adantr.mm"
include "cbs.mm"
include "cfv.mm"
include "cple.mm"
include "equid.mm"
include "wb.mm"
include "simpr.mm"
include "resieq.mm"
include "syl2anc.mm"
include "mpbiri.mm"
include "simplrr.mm"
include "ssbrd.mm"
include "mpd.mm"
include "w3a.mm"
include "wo.mm"
include "wi.mm"
include "pleval2i.mm"
include "3adant1.mm"
include "ancoms.mm"
include "wn.mm"
include "simprl.mm"
include "po2nr.mm"
include "3impb.mm"
include "syl3an1.mm"
include "pm2.21d.mm"
include "simpl.mm"
include "eqcomd.mm"
include "ccased.mm"
include "syl2and.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "potr.mm"
include "sylan.mm"
include "simpll.mm"
include "pltle.mm"
include "syl3anc.mm"
include "syld.mm"
include "breq1.mm"
include "biimpar.mm"
include "syl5.mm"
include "biimpac.mm"
include "syldan.mm"
include "eqtr.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "isposd.mm"
include "ex.mm"
include "impbid2.mm"

theorem pospo
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pospo.b: |- B = ( Base ` K )
  assume pospo.l: |- .<_ = ( le ` K )
  assume pospo.s: |- .< = ( lt ` K )


  assert |- ( K e. V -> ( K e. Poset <-> ( .< Po B /\ ( _I |` B ) C_ .<_ ) ) )

  proof
    cK
    cV
    wcel
    #
    cK
    cpo
    wcel
    #
    cB
    c.lt
    wpo
    #
    cid
    cB
    cres
    #
    c.le
    wss
    #
    wa
    #
    @1
    @2
    @4
    @1
    vx
    vy
    vz
    cB
    c.lt
    cpo
    cB
    c.lt
    cK
    vx
    cv
    #
    pospo.s
    pltirr
    cB
    c.lt
    cK
    @6
    vy
    cv
    #
    vz
    cv
    #
    pospo.b
    pospo.s
    plttr
    ispod
    @1
    vx
    vy
    @3
    c.le
    @3
    wrel
    @1
    cid
    cB
    relres
    a1i
    @6
    @7
    cop
    #
    @3
    wcel
    #
    @6
    cB
    wcel
    #
    @7
    @6
    wceq
    #
    wa
    #
    @1
    @9
    c.le
    wcel
    #
    @10
    @9
    @13
    vx
    vy
    copab
    #
    wcel
    @13
    @15
    @3
    @9
    vx
    vy
    cB
    opabresid
    eleq2i
    @13
    vx
    vy
    opabid
    bitr3i
    @1
    @11
    @12
    @14
    @1
    @11
    wa
    @14
    @12
    @6
    @6
    c.le
    wbr
    #
    cB
    cK
    c.le
    @6
    pospo.b
    pospo.l
    posref
    @14
    @6
    @7
    c.le
    wbr
    #
    @12
    @16
    @6
    @7
    c.le
    df-br
    @7
    @6
    @6
    c.le
    breq2
    syl5bbr
    syl5ibrcom
    expimpd
    syl5bi
    relssdv
    jca
    @0
    @5
    @1
    @0
    @5
    wa
    #
    vx
    vy
    vz
    cB
    cK
    c.le
    @0
    cK
    cvv
    wcel
    @5
    cK
    cV
    elex
    adantr
    cB
    cK
    cbs
    cfv
    wceq
    @18
    pospo.b
    a1i
    c.le
    cK
    cple
    cfv
    wceq
    @18
    pospo.l
    a1i
    @18
    @11
    wa
    #
    @6
    @6
    @3
    wbr
    #
    @16
    @19
    @20
    @6
    @6
    wceq
    #
    vx
    equid
    @19
    @11
    @11
    @20
    @21
    wb
    @18
    @11
    simpr
    #
    @22
    cB
    @6
    @6
    resieq
    syl2anc
    mpbiri
    @19
    @3
    c.le
    @6
    @6
    @0
    @2
    @4
    @11
    simplrr
    ssbrd
    mpd
    #
    @18
    @11
    @7
    cB
    wcel
    #
    w3a
    #
    @17
    @6
    @7
    c.lt
    wbr
    #
    @6
    @7
    wceq
    #
    wo
    #
    @7
    @6
    c.le
    wbr
    #
    @7
    @6
    c.lt
    wbr
    #
    @12
    wo
    #
    @27
    @11
    @24
    @17
    @28
    wi
    #
    @18
    cB
    c.lt
    cK
    c.le
    @6
    @7
    pospo.b
    pospo.l
    pospo.s
    pleval2i
    #
    3adant1
    @11
    @24
    @29
    @31
    wi
    #
    @18
    @24
    @11
    @34
    cB
    c.lt
    cK
    c.le
    @7
    @6
    pospo.b
    pospo.l
    pospo.s
    pleval2i
    ancoms
    3adant1
    @25
    @26
    @30
    @27
    @12
    @27
    @25
    @26
    @30
    wa
    #
    @27
    @18
    @2
    @11
    @24
    @35
    wn
    #
    @0
    @2
    @4
    simprl
    #
    @2
    @11
    @24
    @36
    cB
    @6
    @7
    c.lt
    po2nr
    3impb
    syl3an1
    pm2.21d
    @27
    @30
    wa
    @27
    wi
    @25
    @27
    @30
    simpl
    a1i
    @26
    @12
    wa
    #
    @27
    wi
    @25
    @38
    @7
    @6
    @26
    @12
    simpr
    eqcomd
    a1i
    @27
    @12
    wa
    @27
    wi
    @25
    @27
    @12
    simpl
    a1i
    ccased
    syl2and
    @18
    @11
    @24
    @8
    cB
    wcel
    #
    w3a
    #
    wa
    #
    @17
    @28
    @7
    @8
    c.le
    wbr
    #
    @7
    @8
    c.lt
    wbr
    #
    @7
    @8
    wceq
    #
    wo
    #
    @6
    @8
    c.le
    wbr
    #
    @41
    @11
    @24
    @32
    @18
    @11
    @24
    @39
    simpr1
    #
    @18
    @11
    @24
    @39
    simpr2
    #
    @33
    syl2anc
    @41
    @24
    @39
    @42
    @45
    wi
    @48
    @18
    @11
    @24
    @39
    simpr3
    #
    cB
    c.lt
    cK
    c.le
    @7
    @8
    pospo.b
    pospo.l
    pospo.s
    pleval2i
    syl2anc
    @41
    @26
    @43
    @27
    @44
    @46
    @41
    @26
    @43
    wa
    #
    @6
    @8
    c.lt
    wbr
    #
    @46
    @18
    @2
    @40
    @50
    @51
    wi
    @37
    cB
    @6
    @7
    @8
    c.lt
    potr
    sylan
    @41
    @0
    @11
    @39
    @51
    @46
    wi
    @0
    @5
    @40
    simpll
    @47
    @49
    cV
    cB
    cB
    c.lt
    cK
    c.le
    @6
    @8
    pospo.l
    pospo.s
    pltle
    syl3anc
    #
    syld
    @27
    @43
    wa
    @51
    @41
    @46
    @27
    @51
    @43
    @6
    @7
    @8
    c.lt
    breq1
    biimpar
    @52
    syl5
    @26
    @44
    wa
    @51
    @41
    @46
    @44
    @26
    @51
    @7
    @8
    @6
    c.lt
    breq2
    biimpac
    @52
    syl5
    @41
    @16
    @27
    @44
    wa
    #
    @46
    @18
    @40
    @11
    @16
    @47
    @23
    syldan
    @53
    @6
    @8
    @6
    c.le
    @6
    @7
    @8
    eqtr
    breq2d
    syl5ibcom
    ccased
    syl2and
    isposd
    ex
    impbid2
end
