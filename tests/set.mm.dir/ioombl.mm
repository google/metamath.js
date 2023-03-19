include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "cvol.mm"
include "cdm.mm"
include "clt.mm"
include "wbr.mm"
include "cmnf.mm"
include "wceq.mm"
include "cico.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "snunioo.mm"
include "3expa.mm"
include "adantrr.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wb.mm"
include "lbico1.mm"
include "snssd.mm"
include "cicc.mm"
include "iccid.mm"
include "ad2antrr.mm"
include "ineq1d.mm"
include "simpll.mm"
include "simplr.mm"
include "cle.mm"
include "df-icc.mm"
include "df-ioo.mm"
include "cv.mm"
include "xrltnle.mm"
include "ixxdisj.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "uneqdifeq.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "simprr.mm"
include "simprl.mm"
include "xrre2.mm"
include "syl32anc.mm"
include "icombl.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "ovolsn.mm"
include "syl.mm"
include "nulmbl.mm"
include "difmbl.mm"
include "eqeltrrd.mm"
include "expr.mm"
include "cpnf.mm"
include "uncom.mm"
include "pnfxr.mm"
include "mnfle.mm"
include "simpr.mm"
include "xrlelttrd.mm"
include "pnfge.mm"
include "df-ico.mm"
include "xrlenlt.mm"
include "xrltletr.mm"
include "ixxun.mm"
include "syl5eq.mm"
include "ioomax.mm"
include "syl6eq.mm"
include "ssun1.mm"
include "syl5sseq.mm"
include "incom.mm"
include "rembl.mm"
include "wo.mm"
include "xrleloe.mm"
include "sylancl.mm"
include "wi.mm"
include "w3a.mm"
include "mp3anl3.mm"
include "orim1d.mm"
include "mpd.mm"
include "icombl1.mm"
include "oveq1.mm"
include "ax-mp.mm"
include "ico0.mm"
include "mp2an.mm"
include "mpbir.mm"
include "0mbl.mm"
include "syl6eqel.mm"
include "jaoi.mm"
include "sylancr.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "mpjaod.mm"
include "wn.mm"
include "ioo0.mm"
include "ancoms.mm"
include "bitrd.mm"
include "biimpar.mm"
include "pm2.61dan.mm"
include "ndmioo.mm"
include "pm2.61i.mm"

theorem ioombl
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A (,) B ) e. dom vol

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    cioo
    co
    #
    cvol
    cdm
    #
    wcel
    #
    @2
    cA
    cB
    clt
    wbr
    #
    @5
    @2
    @6
    wa
    #
    cmnf
    cA
    clt
    wbr
    #
    @5
    cmnf
    cA
    wceq
    #
    @2
    @6
    @8
    @5
    @2
    @6
    @8
    wa
    #
    wa
    #
    cA
    cB
    cico
    co
    #
    cA
    csn
    #
    cdif
    #
    @3
    @4
    @11
    @13
    @3
    cun
    @12
    wceq
    #
    @14
    @3
    wceq
    #
    @2
    @6
    @15
    @8
    @0
    @1
    @6
    @15
    cA
    cB
    snunioo
    3expa
    adantrr
    @11
    @13
    @12
    wss
    @13
    @3
    cin
    #
    c0
    wceq
    @15
    @16
    wb
    @11
    cA
    @12
    @2
    @6
    cA
    @12
    wcel
    #
    @8
    @0
    @1
    @6
    @18
    cA
    cB
    lbico1
    3expa
    adantrr
    snssd
    @11
    cA
    cA
    cicc
    co
    #
    @3
    cin
    #
    @17
    c0
    @11
    @19
    @13
    @3
    @0
    @19
    @13
    wceq
    @1
    @10
    cA
    iccid
    ad2antrr
    ineq1d
    @11
    @0
    @0
    @1
    @20
    c0
    wceq
    @0
    @1
    @10
    simpll
    #
    @21
    @0
    @1
    @10
    simplr
    #
    vx
    vy
    vz
    vw
    cA
    cA
    cB
    cioo
    cle
    cle
    clt
    clt
    cicc
    vx
    vy
    vz
    df-icc
    vx
    vy
    vz
    df-ioo
    #
    cA
    vw
    cv
    #
    xrltnle
    ixxdisj
    syl3anc
    eqtr3d
    @13
    @3
    @12
    uneqdifeq
    syl2anc
    mpbid
    @11
    @12
    @4
    wcel
    #
    @13
    @4
    wcel
    #
    @14
    @4
    wcel
    @11
    cA
    cr
    wcel
    #
    @1
    @25
    @11
    cmnf
    cxr
    wcel
    #
    @0
    @1
    @8
    @6
    @27
    @28
    @11
    mnfxr
    a1i
    @21
    @22
    @2
    @6
    @8
    simprr
    @2
    @6
    @8
    simprl
    cmnf
    cA
    cB
    xrre2
    syl32anc
    #
    @22
    cA
    cB
    icombl
    syl2anc
    @11
    @13
    cr
    wss
    @13
    covol
    cfv
    cc0
    wceq
    #
    @26
    @11
    cA
    cr
    @29
    snssd
    @11
    @27
    @30
    @29
    cA
    ovolsn
    syl
    @13
    nulmbl
    syl2anc
    @12
    @13
    difmbl
    syl2anc
    eqeltrrd
    expr
    @7
    cmnf
    cB
    cioo
    co
    #
    @4
    wcel
    @9
    @5
    @7
    cr
    cB
    cpnf
    cico
    co
    #
    cdif
    #
    @31
    @4
    @7
    @32
    @31
    cun
    #
    cr
    wceq
    #
    @33
    @31
    wceq
    #
    @7
    @34
    cmnf
    cpnf
    cioo
    co
    #
    cr
    @7
    @34
    @31
    @32
    cun
    #
    @37
    @32
    @31
    uncom
    @7
    @28
    @1
    cpnf
    cxr
    wcel
    #
    cmnf
    cB
    clt
    wbr
    cB
    cpnf
    cle
    wbr
    #
    @38
    @37
    wceq
    @28
    @7
    mnfxr
    a1i
    #
    @0
    @1
    @6
    simplr
    #
    @39
    @7
    pnfxr
    a1i
    #
    @7
    cmnf
    cA
    cB
    @41
    @0
    @1
    @6
    simpll
    #
    @42
    @0
    cmnf
    cA
    cle
    wbr
    #
    @1
    @6
    cA
    mnfle
    ad2antrr
    #
    @2
    @6
    simpr
    xrlelttrd
    @7
    @1
    @40
    @42
    cB
    pnfge
    syl
    #
    vx
    vy
    vz
    vw
    cmnf
    cB
    cpnf
    cico
    cioo
    clt
    clt
    cle
    clt
    cioo
    clt
    cle
    @23
    vx
    vy
    vz
    df-ico
    #
    cB
    @24
    xrlenlt
    #
    @23
    @24
    cB
    cpnf
    xrltletr
    cmnf
    cB
    @24
    xrltletr
    ixxun
    syl32anc
    syl5eq
    ioomax
    syl6eq
    #
    @7
    @32
    cr
    wss
    @32
    @31
    cin
    #
    c0
    wceq
    @35
    @36
    wb
    @7
    @34
    @32
    cr
    @32
    @31
    ssun1
    @50
    syl5sseq
    @7
    @51
    @31
    @32
    cin
    #
    c0
    @32
    @31
    incom
    @7
    @28
    @1
    @39
    @52
    c0
    wceq
    @41
    @42
    @43
    vx
    vy
    vz
    vw
    cmnf
    cB
    cpnf
    cico
    clt
    clt
    cle
    clt
    cioo
    @23
    @48
    @49
    ixxdisj
    syl3anc
    syl5eq
    @32
    @31
    cr
    uneqdifeq
    syl2anc
    mpbid
    @7
    cr
    @4
    wcel
    @32
    @4
    wcel
    #
    @33
    @4
    wcel
    rembl
    @7
    cB
    cr
    wcel
    #
    cB
    cpnf
    wceq
    #
    wo
    #
    @53
    @7
    cB
    cpnf
    clt
    wbr
    #
    @55
    wo
    #
    @56
    @7
    @40
    @58
    @47
    @7
    @1
    @39
    @40
    @58
    wb
    @42
    pnfxr
    cB
    cpnf
    xrleloe
    sylancl
    mpbid
    @7
    @57
    @54
    @55
    @0
    @1
    @39
    @6
    @57
    @54
    wi
    pnfxr
    @0
    @1
    @39
    w3a
    @6
    @57
    @54
    cA
    cB
    cpnf
    xrre2
    expr
    mp3anl3
    orim1d
    mpd
    @54
    @53
    @55
    cB
    icombl1
    @55
    @32
    c0
    @4
    @55
    @32
    cpnf
    cpnf
    cico
    co
    #
    c0
    cB
    cpnf
    cpnf
    cico
    oveq1
    @59
    c0
    wceq
    #
    cpnf
    cpnf
    cle
    wbr
    #
    @39
    @61
    pnfxr
    cpnf
    pnfge
    ax-mp
    @39
    @39
    @60
    @61
    wb
    pnfxr
    pnfxr
    cpnf
    cpnf
    ico0
    mp2an
    mpbir
    syl6eq
    0mbl
    syl6eqel
    jaoi
    syl
    cr
    @32
    difmbl
    sylancr
    eqeltrrd
    @9
    @31
    @3
    @4
    cmnf
    cA
    cB
    cioo
    oveq1
    eleq1d
    syl5ibcom
    @7
    @45
    @8
    @9
    wo
    #
    @46
    @7
    @28
    @0
    @45
    @62
    wb
    mnfxr
    @44
    cmnf
    cA
    xrleloe
    sylancr
    mpbid
    mpjaod
    @2
    @6
    wn
    #
    wa
    @3
    c0
    @4
    @2
    @3
    c0
    wceq
    #
    @63
    @2
    @64
    cB
    cA
    cle
    wbr
    #
    @63
    cA
    cB
    ioo0
    @1
    @0
    @65
    @63
    wb
    cB
    cA
    xrlenlt
    ancoms
    bitrd
    biimpar
    0mbl
    syl6eqel
    pm2.61dan
    @2
    wn
    @3
    c0
    @4
    cA
    cB
    ndmioo
    0mbl
    syl6eqel
    pm2.61i
end
