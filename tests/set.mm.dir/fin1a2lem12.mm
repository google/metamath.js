include "cpw.mm"
include "wss.mm"
include "crpss.mm"
include "wor.mm"
include "cuni.mm"
include "wcel.mm"
include "wn.mm"
include "w3a.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfin3.mm"
include "com.mm"
include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "cfv.mm"
include "csuc.mm"
include "wral.mm"
include "simpr.mm"
include "simpll1.mm"
include "adantr.mm"
include "ssrab2.mm"
include "unissi.mm"
include "sspwuni.mm"
include "biimpi.mm"
include "syl5ss.mm"
include "syl.mm"
include "wb.mm"
include "elpw2g.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "eqid.mm"
include "fmptd.mm"
include "wi.mm"
include "cvv.mm"
include "vex.mm"
include "sucex.mm"
include "sssucid.mm"
include "ssdomg.mm"
include "mp2.mm"
include "domtr.mm"
include "mpan2.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "uniss.mm"
include "mp1i.mm"
include "wceq.mm"
include "id.mm"
include "pwexg.mm"
include "adantl.mm"
include "ssexd.mm"
include "rabexg.mm"
include "uniexg.mm"
include "3syl.mm"
include "breq2.mm"
include "rabbidv.mm"
include "unieqd.mm"
include "fvmptg.mm"
include "syl2anr.mm"
include "peano2.mm"
include "3sstr4d.mm"
include "ralrimiva.mm"
include "fin34i.mm"
include "syl3anc.mm"
include "csn.mm"
include "cun.mm"
include "fin1a2lem11.mm"
include "adantrr.mm"
include "3ad2antl2.mm"
include "wo.mm"
include "simpll3.mm"
include "simplrr.mm"
include "ss0b.mm"
include "bitri.mm"
include "pw0.mm"
include "sseq2i.mm"
include "sssn.mm"
include "df-ne.mm"
include "0ex.mm"
include "unisn.mm"
include "snid.mm"
include "eqeltri.mm"
include "unieq.mm"
include "eleq12d.mm"
include "mpbiri.mm"
include "orim2i.mm"
include "ord.mm"
include "syl5bi.mm"
include "sylbi.mm"
include "sylbir.mm"
include "com12.mm"
include "con3d.mm"
include "sylc.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "uniun.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtri.mm"
include "eleq1i.mm"
include "elun.mm"
include "elsn2.mm"
include "orbi2i.mm"
include "3bitri.mm"
include "sylnibr.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "mpd.mm"
include "pm2.65da.mm"

theorem fin1a2lem12
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  let cX: class X
  let cC: class C


  assert |- ( ( ( A C_ ~P B /\ [C.] Or A /\ -. U. A e. A ) /\ ( A C_ Fin /\ A =/= (/) ) ) -> -. B e. Fin3 )

  proof
    cA
    cB
    cpw
    #
    wss
    #
    cA
    crpss
    wor
    #
    cA
    cuni
    #
    cA
    wcel
    #
    wn
    #
    w3a
    #
    cA
    cfn
    wss
    #
    cA
    c0
    wne
    #
    wa
    #
    wa
    #
    cB
    cfin3
    wcel
    #
    ve
    com
    vf
    cv
    #
    ve
    cv
    #
    cdom
    wbr
    #
    vf
    cA
    crab
    #
    cuni
    #
    cmpt
    #
    crn
    #
    cuni
    #
    @18
    wcel
    #
    @10
    @11
    wa
    #
    @11
    com
    @0
    @17
    wf
    vd
    cv
    #
    @17
    cfv
    #
    @22
    csuc
    #
    @17
    cfv
    #
    wss
    #
    vd
    com
    wral
    @20
    @10
    @11
    simpr
    @21
    ve
    com
    @16
    @0
    @17
    @21
    @13
    com
    wcel
    #
    wa
    #
    @16
    @0
    wcel
    #
    @16
    cB
    wss
    #
    @28
    @1
    @30
    @21
    @1
    @27
    @1
    @2
    @5
    @9
    @11
    simpll1
    #
    adantr
    @1
    @16
    @3
    cB
    @15
    cA
    @14
    vf
    cA
    ssrab2
    unissi
    @1
    @3
    cB
    wss
    cA
    cB
    sspwuni
    biimpi
    syl5ss
    syl
    @11
    @29
    @30
    wb
    @10
    @27
    @16
    cB
    cfin3
    elpw2g
    ad2antlr
    mpbird
    @17
    eqid
    #
    fmptd
    @21
    @26
    vd
    com
    @21
    @22
    com
    wcel
    #
    wa
    #
    @12
    @22
    cdom
    wbr
    #
    vf
    cA
    crab
    #
    cuni
    #
    @12
    @24
    cdom
    wbr
    #
    vf
    cA
    crab
    #
    cuni
    #
    @23
    @25
    @36
    @39
    wss
    @37
    @40
    wss
    @34
    @35
    @38
    vf
    cA
    @35
    @38
    wi
    @12
    cA
    wcel
    @35
    @22
    @24
    cdom
    wbr
    #
    @38
    @24
    cvv
    wcel
    @22
    @24
    wss
    @41
    @22
    vd
    vex
    sucex
    @22
    sssucid
    @22
    @24
    cvv
    ssdomg
    mp2
    @12
    @22
    @24
    domtr
    mpan2
    a1i
    ss2rabi
    @36
    @39
    uniss
    mp1i
    @33
    @33
    @37
    cvv
    wcel
    #
    @23
    @37
    wceq
    @21
    @33
    id
    @21
    cA
    cvv
    wcel
    #
    @36
    cvv
    wcel
    @42
    @21
    cA
    @0
    cvv
    @11
    @0
    cvv
    wcel
    @10
    cB
    cfin3
    pwexg
    adantl
    @31
    ssexd
    #
    @35
    vf
    cA
    cvv
    rabexg
    @36
    cvv
    uniexg
    3syl
    ve
    @22
    @16
    @37
    com
    cvv
    @17
    @13
    @22
    wceq
    #
    @15
    @36
    @45
    @14
    @35
    vf
    cA
    @13
    @22
    @12
    cdom
    breq2
    rabbidv
    unieqd
    @32
    fvmptg
    syl2anr
    @33
    @24
    com
    wcel
    @40
    cvv
    wcel
    #
    @25
    @40
    wceq
    @21
    @22
    peano2
    @21
    @43
    @39
    cvv
    wcel
    @46
    @44
    @38
    vf
    cA
    cvv
    rabexg
    @39
    cvv
    uniexg
    3syl
    ve
    @24
    @16
    @40
    com
    cvv
    @17
    @13
    @24
    wceq
    #
    @15
    @39
    @47
    @14
    @38
    vf
    cA
    @13
    @24
    @12
    cdom
    breq2
    rabbidv
    unieqd
    @32
    fvmptg
    syl2anr
    3sstr4d
    ralrimiva
    vd
    cB
    @17
    fin34i
    syl3anc
    @21
    @18
    cA
    c0
    csn
    #
    cun
    #
    wceq
    #
    @20
    wn
    #
    @10
    @50
    @11
    @2
    @1
    @9
    @50
    @5
    @2
    @7
    @50
    @8
    cA
    ve
    vf
    fin1a2lem11
    adantrr
    3ad2antl2
    adantr
    @21
    @51
    @50
    @49
    cuni
    #
    @49
    wcel
    #
    wn
    @21
    @4
    @3
    c0
    wceq
    #
    wo
    #
    @53
    @21
    @5
    @54
    wn
    #
    @55
    wn
    @1
    @2
    @5
    @9
    @11
    simpll3
    #
    @21
    @8
    @5
    @56
    @6
    @7
    @8
    @11
    simplrr
    @57
    @8
    @54
    @4
    @54
    @8
    @4
    @54
    cA
    c0
    cpw
    #
    wss
    #
    @8
    @4
    wi
    #
    @59
    @3
    c0
    wss
    @54
    cA
    c0
    sspwuni
    @3
    ss0b
    bitri
    @59
    cA
    c0
    wceq
    #
    cA
    @48
    wceq
    #
    wo
    #
    @60
    @59
    cA
    @48
    wss
    @63
    @58
    @48
    cA
    pw0
    sseq2i
    cA
    c0
    sssn
    bitri
    @8
    @61
    wn
    @63
    @4
    cA
    c0
    df-ne
    @63
    @61
    @4
    @62
    @4
    @61
    @62
    @4
    @48
    cuni
    #
    @48
    wcel
    @64
    c0
    @48
    c0
    0ex
    unisn
    #
    c0
    0ex
    snid
    eqeltri
    @62
    @3
    @64
    cA
    @48
    cA
    @48
    unieq
    @62
    id
    eleq12d
    mpbiri
    orim2i
    ord
    syl5bi
    sylbi
    sylbir
    com12
    con3d
    sylc
    @4
    @54
    ioran
    sylanbrc
    @53
    @3
    @49
    wcel
    @4
    @3
    @48
    wcel
    #
    wo
    @55
    @52
    @3
    @49
    @52
    @3
    @64
    cun
    @3
    c0
    cun
    @3
    cA
    @48
    uniun
    @64
    c0
    @3
    @65
    uneq2i
    @3
    un0
    3eqtri
    eleq1i
    @3
    cA
    @48
    elun
    @66
    @54
    @4
    @3
    c0
    0ex
    elsn2
    orbi2i
    3bitri
    sylnibr
    @50
    @20
    @53
    @50
    @19
    @52
    @18
    @49
    @18
    @49
    unieq
    @50
    id
    eleq12d
    notbid
    syl5ibrcom
    mpd
    pm2.65da
end
