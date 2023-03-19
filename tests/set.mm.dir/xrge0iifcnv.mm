include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cpnf.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cv.mm"
include "wceq.mm"
include "cneg.mm"
include "ce.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "wa.mm"
include "wtru.mm"
include "clog.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "0lepnf.mm"
include "ubicc2.mm"
include "mp3an.mm"
include "a1i.mm"
include "wn.mm"
include "cico.mm"
include "icossicc.mm"
include "cioc.mm"
include "csn.mm"
include "wo.mm"
include "wi.mm"
include "cun.mm"
include "uncom.mm"
include "1re.mm"
include "rexri.mm"
include "0le1.mm"
include "snunioc.mm"
include "eqtr3i.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitr3i.mm"
include "pm2.53.mm"
include "sylbi.mm"
include "elsni.mm"
include "syl6.mm"
include "con1d.mm"
include "imp.mm"
include "clt.mm"
include "crp.mm"
include "cioo.mm"
include "wss.mm"
include "0le0.mm"
include "cr.mm"
include "ltpnf.mm"
include "ax-mp.mm"
include "iocssioo.mm"
include "mp4an.mm"
include "ioorp.mm"
include "sseqtri.mm"
include "sseli.mm"
include "relogcld.mm"
include "renegcld.mm"
include "rexrd.mm"
include "w3a.mm"
include "wb.mm"
include "elioc1.mm"
include "mp2an.mm"
include "simp3bi.mm"
include "1rp.mm"
include "logled.mm"
include "mpbid.mm"
include "log1.mm"
include "syl6breq.mm"
include "le0neg1d.mm"
include "syl.mm"
include "elico1.mm"
include "syl3anbrc.mm"
include "sseldi.mm"
include "ifclda.mm"
include "adantl.mm"
include "0elunit.mm"
include "iocssicc.mm"
include "snunico.mm"
include "rge0ssre.mm"
include "reefcld.mm"
include "efgt0.mm"
include "simp2bi.mm"
include "le0neg2d.mm"
include "0re.mm"
include "efle.mm"
include "sylancl.mm"
include "ef0.mm"
include "eqeq2.mm"
include "bibi1d.mm"
include "simpr.mm"
include "iftrue.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "wnel.mm"
include "ubico.mm"
include "nelir.mm"
include "neleq1.mm"
include "mpbiri.mm"
include "syl5ibcom.mm"
include "df-nel.mm"
include "iffalse.mm"
include "eqeltrd.mm"
include "ex.mm"
include "ad2antrr.mm"
include "syl5bi.mm"
include "syld.mm"
include "impbid.mm"
include "bibi2d.mm"
include "wne.mm"
include "ltned.mm"
include "adantll.mm"
include "neneqd.mm"
include "eqeq1.mm"
include "notbid.mm"
include "simplr.mm"
include "2falsed.mm"
include "eqcom.mm"
include "relogeftb.mm"
include "syl2an.mm"
include "cc.mm"
include "recnd.mm"
include "negcon2.mm"
include "3bitr2d.mm"
include "an4s.mm"
include "anass1rs.mm"
include "ifbothda.mm"
include "f1ocnv2d.mm"
include "trud.mm"

theorem xrge0iifcnv
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  assume xrge0iifhmeo.1: |- F = ( x e. ( 0 [,] 1 ) |-> if ( x = 0 , +oo , -u ( log ` x ) ) )

  disjoint x y
  assert |- ( F : ( 0 [,] 1 ) -1-1-onto-> ( 0 [,] +oo ) /\ `' F = ( y e. ( 0 [,] +oo ) |-> if ( y = +oo , 0 , ( exp ` -u y ) ) ) )

  proof
    cc0
    c1
    cicc
    co
    #
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf1o
    cF
    ccnv
    vy
    @1
    vy
    cv
    #
    cpnf
    wceq
    #
    cc0
    @2
    cneg
    #
    ce
    cfv
    #
    cif
    #
    cmpt
    wceq
    wa
    wtru
    vx
    vy
    @0
    @1
    vx
    cv
    #
    cc0
    wceq
    #
    cpnf
    @7
    clog
    cfv
    #
    cneg
    #
    cif
    #
    @6
    cF
    xrge0iifhmeo.1
    @7
    @0
    wcel
    #
    @11
    @1
    wcel
    wtru
    @12
    @8
    cpnf
    @10
    @1
    cpnf
    @1
    wcel
    #
    @12
    @8
    wa
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    cc0
    cpnf
    cle
    wbr
    #
    @13
    0xr
    pnfxr
    0lepnf
    cc0
    cpnf
    ubicc2
    mp3an
    a1i
    @12
    @8
    wn
    #
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    @1
    @10
    cc0
    cpnf
    icossicc
    @18
    @7
    cc0
    c1
    cioc
    co
    #
    wcel
    #
    @10
    @19
    wcel
    #
    @12
    @17
    @21
    @12
    @21
    @8
    @12
    @21
    wn
    #
    @7
    cc0
    csn
    #
    wcel
    #
    @8
    @12
    @21
    @25
    wo
    #
    @23
    @25
    wi
    @12
    @7
    @20
    @24
    cun
    #
    wcel
    @26
    @27
    @0
    @7
    @24
    @20
    cun
    #
    @27
    @0
    @24
    @20
    uncom
    @14
    c1
    cxr
    wcel
    #
    cc0
    c1
    cle
    wbr
    @28
    @0
    wceq
    0xr
    c1
    1re
    rexri
    #
    0le1
    cc0
    c1
    snunioc
    mp3an
    eqtr3i
    eleq2i
    @7
    @20
    @24
    elun
    bitr3i
    @21
    @25
    pm2.53
    sylbi
    @7
    cc0
    elsni
    syl6
    con1d
    imp
    #
    @21
    @10
    cxr
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    @10
    cpnf
    clt
    wbr
    #
    @22
    @21
    @10
    @21
    @9
    @21
    @7
    @20
    crp
    @7
    @20
    cc0
    cpnf
    cioo
    co
    #
    crp
    @14
    @15
    cc0
    cc0
    cle
    wbr
    c1
    cpnf
    clt
    wbr
    #
    @20
    @35
    wss
    0xr
    pnfxr
    0le0
    c1
    cr
    wcel
    @36
    1re
    c1
    ltpnf
    ax-mp
    cc0
    cpnf
    cc0
    c1
    iocssioo
    mp4an
    ioorp
    sseqtri
    sseli
    #
    relogcld
    #
    renegcld
    #
    rexrd
    @21
    @9
    cc0
    cle
    wbr
    @33
    @21
    @9
    c1
    clog
    cfv
    #
    cc0
    cle
    @21
    @7
    c1
    cle
    wbr
    #
    @9
    @40
    cle
    wbr
    @21
    @7
    cxr
    wcel
    #
    cc0
    @7
    clt
    wbr
    #
    @41
    @14
    @29
    @21
    @42
    @43
    @41
    w3a
    wb
    0xr
    @30
    cc0
    c1
    @7
    elioc1
    mp2an
    simp3bi
    @21
    @7
    c1
    @37
    c1
    crp
    wcel
    @21
    1rp
    a1i
    logled
    mpbid
    log1
    syl6breq
    @21
    @9
    @38
    le0neg1d
    mpbid
    @21
    @10
    cr
    wcel
    @34
    @39
    @10
    ltpnf
    syl
    @14
    @15
    @22
    @32
    @33
    @34
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @10
    elico1
    mp2an
    syl3anbrc
    syl
    #
    sseldi
    ifclda
    adantl
    @2
    @1
    wcel
    #
    @6
    @0
    wcel
    wtru
    @45
    @3
    cc0
    @5
    @0
    cc0
    @0
    wcel
    @45
    @3
    wa
    0elunit
    a1i
    @45
    @3
    wn
    #
    wa
    #
    @20
    @0
    @5
    cc0
    c1
    iocssicc
    @47
    @2
    @19
    wcel
    #
    @5
    @20
    wcel
    #
    @45
    @46
    @48
    @45
    @48
    @3
    @45
    @48
    wn
    #
    @2
    cpnf
    csn
    #
    wcel
    #
    @3
    @45
    @48
    @52
    wo
    #
    @50
    @52
    wi
    @45
    @2
    @19
    @51
    cun
    #
    wcel
    @53
    @54
    @1
    @2
    @14
    @15
    @16
    @54
    @1
    wceq
    0xr
    pnfxr
    0lepnf
    cc0
    cpnf
    snunico
    mp3an
    eleq2i
    @2
    @19
    @51
    elun
    bitr3i
    @48
    @52
    pm2.53
    sylbi
    @2
    cpnf
    elsni
    syl6
    con1d
    imp
    #
    @48
    @5
    cxr
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    @5
    c1
    cle
    wbr
    #
    @49
    @48
    @5
    @48
    @4
    @48
    @2
    @19
    cr
    @2
    rge0ssre
    sseli
    #
    renegcld
    #
    reefcld
    rexrd
    @48
    @4
    cr
    wcel
    #
    @57
    @60
    @4
    efgt0
    syl
    #
    @48
    @5
    cc0
    ce
    cfv
    #
    c1
    cle
    @48
    @4
    cc0
    cle
    wbr
    #
    @5
    @63
    cle
    wbr
    #
    @48
    cc0
    @2
    cle
    wbr
    #
    @64
    @48
    @2
    cxr
    wcel
    #
    @66
    @2
    cpnf
    clt
    wbr
    #
    @14
    @15
    @48
    @67
    @66
    @68
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @2
    elico1
    mp2an
    simp2bi
    @48
    @2
    @59
    le0neg2d
    mpbid
    @48
    @61
    cc0
    cr
    wcel
    #
    @64
    @65
    wb
    @60
    0re
    @4
    cc0
    efle
    sylancl
    mpbid
    ef0
    syl6breq
    @14
    @29
    @49
    @56
    @57
    @58
    w3a
    wb
    0xr
    @30
    cc0
    c1
    @5
    elioc1
    mp2an
    syl3anbrc
    syl
    sseldi
    ifclda
    adantl
    @12
    @45
    wa
    #
    @7
    @6
    wceq
    #
    @2
    @11
    wceq
    #
    wb
    #
    wtru
    @3
    @8
    @72
    wb
    @7
    @5
    wceq
    #
    @72
    wb
    #
    @73
    @70
    cc0
    @5
    cc0
    @6
    wceq
    @8
    @71
    @72
    cc0
    @6
    @7
    eqeq2
    bibi1d
    @5
    @6
    wceq
    @74
    @71
    @72
    @5
    @6
    @7
    eqeq2
    bibi1d
    @70
    @3
    wa
    #
    @8
    @72
    @76
    @72
    @8
    @3
    @70
    @3
    simpr
    @8
    @11
    cpnf
    @2
    @8
    cpnf
    @10
    iftrue
    eqeq2d
    syl5ibrcom
    @76
    @72
    @11
    @19
    wnel
    #
    @8
    @76
    @2
    @19
    wnel
    #
    @72
    @77
    @76
    @78
    cpnf
    @19
    wnel
    #
    cpnf
    @19
    @69
    @15
    cpnf
    @19
    wcel
    wn
    0re
    pnfxr
    cc0
    cpnf
    ubico
    mp2an
    nelir
    @3
    @78
    @79
    wb
    @70
    @2
    cpnf
    @19
    neleq1
    adantl
    mpbiri
    @2
    @11
    @19
    neleq1
    syl5ibcom
    @77
    @11
    @19
    wcel
    #
    wn
    @76
    @8
    @11
    @19
    df-nel
    @76
    @8
    @80
    @12
    @17
    @80
    wi
    @45
    @3
    @12
    @17
    @80
    @18
    @11
    @10
    @19
    @17
    @11
    @10
    wceq
    @12
    @8
    cpnf
    @10
    iffalse
    adantl
    @44
    eqeltrd
    ex
    ad2antrr
    con1d
    syl5bi
    syld
    impbid
    @8
    @74
    @3
    wb
    @74
    @2
    @10
    wceq
    #
    wb
    #
    @75
    @70
    @46
    wa
    #
    cpnf
    @10
    cpnf
    @11
    wceq
    @3
    @72
    @74
    cpnf
    @11
    @2
    eqeq2
    bibi2d
    @10
    @11
    wceq
    @81
    @72
    @74
    @10
    @11
    @2
    eqeq2
    bibi2d
    @83
    @8
    wa
    @74
    @3
    @83
    @8
    @74
    wn
    #
    @83
    @84
    @8
    cc0
    @5
    wceq
    #
    wn
    @83
    cc0
    @5
    @45
    @46
    cc0
    @5
    wne
    @12
    @47
    cc0
    @5
    @69
    @47
    0re
    a1i
    @47
    @48
    @57
    @55
    @62
    syl
    ltned
    adantll
    neneqd
    @8
    @74
    @85
    @7
    cc0
    @5
    eqeq1
    notbid
    syl5ibrcom
    imp
    @70
    @46
    @8
    simplr
    2falsed
    @70
    @17
    @46
    @82
    @12
    @17
    @45
    @46
    @82
    @18
    @21
    @48
    @82
    @47
    @31
    @55
    @21
    @48
    wa
    #
    @74
    @5
    @7
    wceq
    #
    @9
    @4
    wceq
    #
    @81
    @74
    @87
    wb
    @86
    @7
    @5
    eqcom
    a1i
    @21
    @7
    crp
    wcel
    @61
    @88
    @87
    wb
    @48
    @37
    @60
    @7
    @4
    relogeftb
    syl2an
    @21
    @9
    cc
    wcel
    @2
    cc
    wcel
    @88
    @81
    wb
    @48
    @21
    @9
    @38
    recnd
    @48
    @2
    @59
    recnd
    @9
    @2
    negcon2
    syl2an
    3bitr2d
    syl2an
    an4s
    anass1rs
    ifbothda
    ifbothda
    adantl
    f1ocnv2d
    trud
end
