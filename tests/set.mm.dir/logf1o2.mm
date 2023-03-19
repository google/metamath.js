include "clog.mm"
include "cima.mm"
include "cres.mm"
include "wf1o.mm"
include "cim.mm"
include "ccnv.mm"
include "cpi.mm"
include "cneg.mm"
include "cioo.mm"
include "co.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "crn.mm"
include "wf1.mm"
include "wss.mm"
include "logf1o.mm"
include "f1of1.mm"
include "ax-mp.mm"
include "logdmss.mm"
include "f1ores.mm"
include "mp2an.mm"
include "wceq.mm"
include "wb.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wfun.mm"
include "cdm.mm"
include "wral.mm"
include "f1ofun.mm"
include "wf.mm"
include "f1of.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "funimass4.mm"
include "cr.mm"
include "crp.mm"
include "wi.mm"
include "ellogdm.mm"
include "simplbi.mm"
include "logdmn0.mm"
include "logcld.mm"
include "clt.mm"
include "wbr.mm"
include "imcld.mm"
include "cle.mm"
include "logimcld.mm"
include "simpld.mm"
include "wne.mm"
include "wn.mm"
include "logdmnrp.mm"
include "lognegb.mm"
include "syl2anc.mm"
include "necon3bbid.mm"
include "mpbid.mm"
include "necomd.mm"
include "pire.mm"
include "a1i.mm"
include "simprd.mm"
include "leltned.mm"
include "mpbird.mm"
include "cxr.mm"
include "w3a.mm"
include "renegcli.mm"
include "rexri.mm"
include "elioo2.mm"
include "syl3anbrc.mm"
include "wfn.mm"
include "wa.mm"
include "imf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "sylanbrc.mm"
include "mprgbir.mm"
include "ce.mm"
include "simpl.mm"
include "eliooord.mm"
include "adantl.mm"
include "imcl.mm"
include "adantr.mm"
include "ltle.mm"
include "sylancl.mm"
include "mpd.mm"
include "ellogrn.mm"
include "logef.mm"
include "syl.mm"
include "efcl.mm"
include "recnd.mm"
include "picn.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "mulid1i.mm"
include "syl6breqr.mm"
include "1re.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "1e0p1.mm"
include "syl6breq.mm"
include "cz.mm"
include "csin.mm"
include "ccos.mm"
include "ci.mm"
include "recoscld.mm"
include "resincld.mm"
include "crimd.mm"
include "cre.mm"
include "efeul.mm"
include "ad2antrr.mm"
include "oveq1d.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcld.mm"
include "recl.mm"
include "efne0.mm"
include "divcan3d.mm"
include "eqtrd.mm"
include "simpr.mm"
include "reefcld.mm"
include "redivcld.mm"
include "eqeltrrd.mm"
include "reim0d.mm"
include "eqtr3d.mm"
include "sineq0.mm"
include "0z.mm"
include "zleltp1.mm"
include "cmin.mm"
include "df-neg.mm"
include "mulm1i.mm"
include "syl5eqbr.mm"
include "ltmuldiv.mm"
include "syl5eqbrr.mm"
include "zlem1lt.mm"
include "0re.mm"
include "letri3.mm"
include "mpbir2and.mm"
include "diveq0d.mm"
include "reim0b.mm"
include "rpefcld.mm"
include "ex.mm"
include "funfvima2.mm"
include "sylbi.mm"
include "ssriv.mm"
include "eqssi.mm"
include "f1oeq3.mm"
include "mpbi.mm"

theorem logf1o2
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume logcn.d: |- D = ( CC \ ( -oo (,] 0 ) )


  assert |- ( log |` D ) : D -1-1-onto-> ( `' Im " ( -u _pi (,) _pi ) )

  proof
    cD
    clog
    cD
    cima
    #
    clog
    cD
    cres
    #
    wf1o
    #
    cD
    cim
    ccnv
    cpi
    cneg
    #
    cpi
    cioo
    co
    #
    cima
    #
    @1
    wf1o
    #
    cc
    cc0
    csn
    cdif
    #
    clog
    crn
    #
    clog
    wf1
    #
    cD
    @7
    wss
    @2
    @7
    @8
    clog
    wf1o
    #
    @9
    logf1o
    @7
    @8
    clog
    f1of1
    ax-mp
    cD
    logcn.d
    logdmss
    #
    @7
    @8
    cD
    clog
    f1ores
    mp2an
    @0
    @5
    wceq
    @2
    @6
    wb
    @0
    @5
    @0
    @5
    wss
    #
    vx
    cv
    #
    clog
    cfv
    #
    @5
    wcel
    #
    vx
    cD
    clog
    wfun
    #
    cD
    clog
    cdm
    #
    wss
    #
    @12
    @15
    vx
    cD
    wral
    wb
    @10
    @16
    logf1o
    @7
    @8
    clog
    f1ofun
    ax-mp
    #
    cD
    @7
    @17
    @11
    @7
    @8
    clog
    @10
    @7
    @8
    clog
    wf
    logf1o
    @7
    @8
    clog
    f1of
    ax-mp
    fdmi
    sseqtr4i
    #
    vx
    cD
    @5
    clog
    funimass4
    mp2an
    @13
    cD
    wcel
    #
    @14
    cc
    wcel
    #
    @14
    cim
    cfv
    #
    @4
    wcel
    #
    @15
    @21
    @13
    @21
    @13
    cc
    wcel
    #
    @13
    cr
    wcel
    #
    @13
    crp
    wcel
    wi
    @13
    cD
    logcn.d
    ellogdm
    simplbi
    #
    @13
    cD
    logcn.d
    logdmn0
    #
    logcld
    #
    @21
    @23
    cr
    wcel
    #
    @3
    @23
    clt
    wbr
    #
    @23
    cpi
    clt
    wbr
    #
    @24
    @21
    @14
    @29
    imcld
    #
    @21
    @31
    @23
    cpi
    cle
    wbr
    #
    @21
    @13
    @27
    @28
    logimcld
    #
    simpld
    @21
    @32
    cpi
    @23
    wne
    @21
    @23
    cpi
    @21
    @13
    cneg
    crp
    wcel
    #
    wn
    @23
    cpi
    wne
    @13
    cD
    logcn.d
    logdmnrp
    @21
    @36
    @23
    cpi
    @21
    @25
    @13
    cc0
    wne
    @36
    @23
    cpi
    wceq
    wb
    @27
    @28
    @13
    lognegb
    syl2anc
    necon3bbid
    mpbid
    necomd
    @21
    @23
    cpi
    @33
    cpi
    cr
    wcel
    #
    @21
    pire
    a1i
    @21
    @31
    @34
    @35
    simprd
    leltned
    mpbird
    @3
    cxr
    wcel
    cpi
    cxr
    wcel
    @24
    @30
    @31
    @32
    w3a
    wb
    @3
    cpi
    pire
    renegcli
    rexri
    cpi
    pire
    rexri
    @3
    cpi
    @23
    elioo2
    mp2an
    syl3anbrc
    cc
    cr
    cim
    wf
    #
    cim
    cc
    wfn
    #
    @15
    @22
    @24
    wa
    wb
    imf
    cc
    cr
    cim
    ffn
    #
    cc
    @14
    @4
    cim
    elpreima
    mp2b
    sylanbrc
    mprgbir
    vx
    @5
    @0
    @13
    @5
    wcel
    #
    @25
    @13
    cim
    cfv
    #
    @4
    wcel
    #
    wa
    #
    @13
    @0
    wcel
    @38
    @39
    @41
    @44
    wb
    imf
    @40
    cc
    @13
    @4
    cim
    elpreima
    mp2b
    @44
    @13
    ce
    cfv
    #
    clog
    cfv
    #
    @13
    @0
    @44
    @13
    @8
    wcel
    #
    @46
    @13
    wceq
    @44
    @25
    @3
    @42
    clt
    wbr
    #
    @42
    cpi
    cle
    wbr
    #
    @47
    @25
    @43
    simpl
    @44
    @48
    @42
    cpi
    clt
    wbr
    #
    @43
    @48
    @50
    wa
    @25
    @42
    @3
    cpi
    eliooord
    adantl
    #
    simpld
    #
    @44
    @50
    @49
    @44
    @48
    @50
    @51
    simprd
    #
    @44
    @42
    cr
    wcel
    #
    @37
    @50
    @49
    wi
    @25
    @54
    @43
    @13
    imcl
    adantr
    #
    pire
    @42
    cpi
    ltle
    sylancl
    mpd
    @13
    ellogrn
    syl3anbrc
    @13
    logef
    syl
    @44
    @45
    cD
    wcel
    #
    @46
    @0
    wcel
    #
    @44
    @45
    cc
    wcel
    #
    @45
    cr
    wcel
    #
    @45
    crp
    wcel
    #
    wi
    @56
    @25
    @58
    @43
    @13
    efcl
    adantr
    @44
    @59
    @60
    @44
    @59
    wa
    #
    @13
    @61
    @26
    @42
    cc0
    wceq
    #
    @61
    @42
    cpi
    @61
    @42
    @44
    @54
    @59
    @55
    adantr
    #
    recnd
    #
    cpi
    cc
    wcel
    @61
    picn
    a1i
    cpi
    cc0
    wne
    @61
    cpi
    pire
    pipos
    gt0ne0ii
    a1i
    #
    @61
    @42
    cpi
    cdiv
    co
    #
    cc0
    wceq
    #
    @66
    cc0
    cle
    wbr
    #
    cc0
    @66
    cle
    wbr
    #
    @61
    @68
    @66
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @61
    @66
    c1
    @70
    clt
    @61
    @66
    c1
    clt
    wbr
    #
    @42
    cpi
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @61
    @42
    cpi
    @73
    clt
    @44
    @50
    @59
    @53
    adantr
    cpi
    picn
    mulid1i
    syl6breqr
    @61
    @54
    c1
    cr
    wcel
    #
    @37
    cc0
    cpi
    clt
    wbr
    #
    @72
    @74
    wb
    @63
    @75
    @61
    1re
    a1i
    @37
    @61
    pire
    a1i
    #
    @76
    @61
    pipos
    a1i
    #
    @42
    c1
    cpi
    ltdivmul
    syl112anc
    mpbird
    1e0p1
    syl6breq
    @61
    @66
    cz
    wcel
    #
    cc0
    cz
    wcel
    #
    @68
    @71
    wb
    @61
    @42
    csin
    cfv
    #
    cc0
    wceq
    #
    @79
    @61
    @42
    ccos
    cfv
    #
    ci
    @81
    cmul
    co
    #
    caddc
    co
    #
    cim
    cfv
    @81
    cc0
    @61
    @83
    @81
    @61
    @42
    @63
    recoscld
    #
    @61
    @42
    @63
    resincld
    #
    crimd
    @61
    @85
    @61
    @45
    @13
    cre
    cfv
    #
    ce
    cfv
    #
    cdiv
    co
    #
    @85
    cr
    @61
    @90
    @89
    @85
    cmul
    co
    #
    @89
    cdiv
    co
    @85
    @61
    @45
    @91
    @89
    cdiv
    @25
    @45
    @91
    wceq
    @43
    @59
    @13
    efeul
    ad2antrr
    oveq1d
    @61
    @85
    @89
    @61
    @83
    @84
    @61
    @83
    @86
    recnd
    @61
    ci
    cc
    wcel
    @81
    cc
    wcel
    @84
    cc
    wcel
    ax-icn
    @61
    @81
    @87
    recnd
    ci
    @81
    mulcl
    sylancr
    addcld
    @61
    @88
    cc
    wcel
    #
    @89
    cc
    wcel
    @61
    @88
    @25
    @88
    cr
    wcel
    @43
    @59
    @13
    recl
    ad2antrr
    #
    recnd
    #
    @88
    efcl
    syl
    @61
    @92
    @89
    cc0
    wne
    @94
    @88
    efne0
    syl
    #
    divcan3d
    eqtrd
    @61
    @45
    @89
    @44
    @59
    simpr
    @61
    @88
    @93
    reefcld
    @95
    redivcld
    eqeltrrd
    reim0d
    eqtr3d
    @61
    @42
    cc
    wcel
    @82
    @79
    wb
    @64
    @42
    sineq0
    syl
    mpbid
    #
    0z
    @66
    cc0
    zleltp1
    sylancl
    mpbird
    @61
    @69
    cc0
    c1
    cmin
    co
    #
    @66
    clt
    wbr
    #
    @61
    @97
    c1
    cneg
    #
    @66
    clt
    c1
    df-neg
    @61
    @99
    cpi
    cmul
    co
    #
    @42
    clt
    wbr
    #
    @99
    @66
    clt
    wbr
    #
    @61
    @100
    @3
    @42
    clt
    cpi
    picn
    mulm1i
    @44
    @48
    @59
    @52
    adantr
    syl5eqbr
    @61
    @99
    cr
    wcel
    #
    @54
    @37
    @76
    @101
    @102
    wb
    @103
    @61
    c1
    1re
    renegcli
    a1i
    @63
    @77
    @78
    @99
    @42
    cpi
    ltmuldiv
    syl112anc
    mpbid
    syl5eqbrr
    @61
    @80
    @79
    @69
    @98
    wb
    0z
    @96
    cc0
    @66
    zlem1lt
    sylancr
    mpbird
    @61
    @66
    cr
    wcel
    cc0
    cr
    wcel
    @67
    @68
    @69
    wa
    wb
    @61
    @42
    cpi
    @63
    @77
    @65
    redivcld
    0re
    @66
    cc0
    letri3
    sylancl
    mpbir2and
    diveq0d
    @25
    @26
    @62
    wb
    @43
    @59
    @13
    reim0b
    ad2antrr
    mpbird
    rpefcld
    ex
    @45
    cD
    logcn.d
    ellogdm
    sylanbrc
    @16
    @18
    @56
    @57
    wi
    @19
    @20
    cD
    @45
    clog
    funfvima2
    mp2an
    syl
    eqeltrrd
    sylbi
    ssriv
    eqssi
    @0
    @5
    cD
    @1
    f1oeq3
    ax-mp
    mpbi
end
