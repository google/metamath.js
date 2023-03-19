include "cc.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cpi.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "wa.mm"
include "cmo.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cabs.mm"
include "cfl.mm"
include "cneg.mm"
include "cmul.mm"
include "caddc.mm"
include "cmin.mm"
include "cr.mm"
include "crp.mm"
include "ci.mm"
include "c2.mm"
include "ce.mm"
include "c1.mm"
include "sinval.mm"
include "eqeq1d.mm"
include "wb.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "efcl.mm"
include "syl.mm"
include "negicn.mm"
include "subcld.mm"
include "wne.mm"
include "2mulicn.mm"
include "2muline0.mm"
include "diveq0.mm"
include "mp3an23.mm"
include "subeq0ad.mm"
include "3bitrd.mm"
include "oveq2.mm"
include "2cn.mm"
include "mul12.mm"
include "mp3an12.mm"
include "2timesd.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "efadd.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "negidi.mm"
include "oveq1i.mm"
include "adddir.mm"
include "mul02.mm"
include "3eqtr3a.mm"
include "ef0.mm"
include "syl6eq.mm"
include "eqtr3d.mm"
include "eqeq12d.mm"
include "fveq2.mm"
include "syl6bi.mm"
include "syl5.mm"
include "sylbid.mm"
include "abs1.mm"
include "eqeq2i.mm"
include "2re.mm"
include "2ne0.mm"
include "mulre.mm"
include "absefib.mm"
include "bitr2d.mm"
include "syl5bb.mm"
include "sylibd.mm"
include "imp.mm"
include "pirp.mm"
include "modval.mm"
include "sylancl.mm"
include "picn.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "redivcl.mm"
include "flcld.mm"
include "zcnd.mm"
include "sylancr.mm"
include "negsub.mm"
include "syldan.mm"
include "mulcom.mm"
include "negeqd.mm"
include "mulneg1.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "3eqtr2d.mm"
include "znegcld.mm"
include "abssinper.mm"
include "simpr.mm"
include "3eqtrd.mm"
include "abs0.mm"
include "cioo.mm"
include "modcl.mm"
include "modlt.mm"
include "jca.mm"
include "biantrurd.mm"
include "w3a.mm"
include "0re.mm"
include "cxr.mm"
include "rexr.mm"
include "elioo2.mm"
include "syl2an.mm"
include "mp2an.mm"
include "3anan32.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "sinq12gt0.mm"
include "elioore.mm"
include "resincld.mm"
include "cle.mm"
include "wi.mm"
include "ltle.mm"
include "mpd.mm"
include "absidd.mm"
include "breqtrrd.mm"
include "ltne.mm"
include "syl6.mm"
include "necon2bd.mm"
include "wo.mm"
include "modge0.mm"
include "leloe.mm"
include "mpbid.mm"
include "ord.mm"
include "eqcomd.mm"
include "mod0.mm"
include "divcan1.mm"
include "sinkpi.mm"
include "sylan9req.mm"
include "impbida.mm"

theorem sineq0
  let cA: class A


  assert |- ( A e. CC -> ( ( sin ` A ) = 0 <-> ( A / _pi ) e. ZZ ) )

  proof
    cA
    cc
    wcel
    #
    cA
    csin
    cfv
    #
    cc0
    wceq
    #
    cA
    cpi
    cdiv
    co
    #
    cz
    wcel
    #
    @0
    @2
    wa
    #
    cA
    cpi
    cmo
    co
    #
    cc0
    wceq
    #
    @4
    @5
    cc0
    @6
    @5
    cc0
    @6
    clt
    wbr
    #
    wn
    #
    cc0
    @6
    wceq
    #
    @5
    @6
    csin
    cfv
    #
    cabs
    cfv
    #
    cc0
    wceq
    @9
    @5
    @12
    cc0
    cabs
    cfv
    #
    cc0
    @5
    @12
    cA
    @3
    cfl
    cfv
    #
    cneg
    #
    cpi
    cmul
    co
    #
    caddc
    co
    #
    csin
    cfv
    #
    cabs
    cfv
    #
    @1
    cabs
    cfv
    #
    @13
    @5
    @11
    @18
    cabs
    @5
    @6
    @17
    csin
    @5
    @6
    cA
    cpi
    @14
    cmul
    co
    #
    cmin
    co
    #
    cA
    @21
    cneg
    #
    caddc
    co
    #
    @17
    @5
    cA
    cr
    wcel
    #
    cpi
    crp
    wcel
    #
    @6
    @22
    wceq
    @0
    @2
    @25
    @0
    @2
    ci
    c2
    cA
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cabs
    cfv
    #
    c1
    cabs
    cfv
    #
    wceq
    #
    @25
    @0
    @2
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    cA
    cmul
    co
    #
    ce
    cfv
    #
    wceq
    #
    @32
    @0
    @2
    @34
    @37
    cmin
    co
    #
    c2
    ci
    cmul
    co
    #
    cdiv
    co
    #
    cc0
    wceq
    #
    @39
    cc0
    wceq
    #
    @38
    @0
    @1
    @41
    cc0
    cA
    sinval
    eqeq1d
    @0
    @39
    cc
    wcel
    #
    @42
    @43
    wb
    #
    @0
    @34
    @37
    @0
    @33
    cc
    wcel
    #
    @34
    cc
    wcel
    ci
    cc
    wcel
    #
    @0
    @46
    ax-icn
    ci
    cA
    mulcl
    mpan
    #
    @33
    efcl
    syl
    #
    @0
    @36
    cc
    wcel
    #
    @37
    cc
    wcel
    @35
    cc
    wcel
    #
    @0
    @50
    negicn
    @35
    cA
    mulcl
    mpan
    #
    @36
    efcl
    syl
    #
    subcld
    @44
    @40
    cc
    wcel
    @40
    cc0
    wne
    @45
    2mulicn
    2muline0
    @39
    @40
    diveq0
    mp3an23
    syl
    @0
    @34
    @37
    @49
    @53
    subeq0ad
    3bitrd
    @38
    @34
    @34
    cmul
    co
    #
    @34
    @37
    cmul
    co
    #
    wceq
    #
    @0
    @32
    @34
    @37
    @34
    cmul
    oveq2
    @0
    @56
    @29
    c1
    wceq
    @32
    @0
    @54
    @29
    @55
    c1
    @0
    @29
    @33
    @33
    caddc
    co
    #
    ce
    cfv
    #
    @54
    @0
    @28
    @57
    ce
    @0
    @28
    c2
    @33
    cmul
    co
    #
    @57
    @47
    c2
    cc
    wcel
    #
    @0
    @28
    @59
    wceq
    ax-icn
    2cn
    ci
    c2
    cA
    mul12
    mp3an12
    @0
    @33
    @48
    2timesd
    eqtrd
    fveq2d
    @0
    @46
    @46
    @58
    @54
    wceq
    @48
    @48
    @33
    @33
    efadd
    syl2anc
    eqtr2d
    @0
    @33
    @36
    caddc
    co
    #
    ce
    cfv
    #
    @55
    c1
    @0
    @46
    @50
    @62
    @55
    wceq
    @48
    @52
    @33
    @36
    efadd
    syl2anc
    @0
    @62
    cc0
    ce
    cfv
    c1
    @0
    @61
    cc0
    ce
    @0
    ci
    @35
    caddc
    co
    #
    cA
    cmul
    co
    #
    cc0
    cA
    cmul
    co
    @61
    cc0
    @63
    cc0
    cA
    cmul
    ci
    ax-icn
    negidi
    oveq1i
    @47
    @51
    @0
    @64
    @61
    wceq
    ax-icn
    negicn
    ci
    @35
    cA
    adddir
    mp3an12
    cA
    mul02
    3eqtr3a
    fveq2d
    ef0
    syl6eq
    eqtr3d
    eqeq12d
    @29
    c1
    cabs
    fveq2
    syl6bi
    syl5
    sylbid
    @32
    @30
    c1
    wceq
    #
    @0
    @25
    @31
    c1
    @30
    abs1
    eqeq2i
    @0
    @25
    @27
    cr
    wcel
    #
    @65
    @0
    c2
    cr
    wcel
    c2
    cc0
    wne
    @25
    @66
    wb
    2re
    2ne0
    cA
    c2
    mulre
    mp3an23
    @0
    @27
    cc
    wcel
    #
    @66
    @65
    wb
    @60
    @0
    @67
    2cn
    c2
    cA
    mulcl
    mpan
    @27
    absefib
    syl
    bitr2d
    syl5bb
    sylibd
    imp
    #
    pirp
    cA
    cpi
    modval
    sylancl
    @0
    @2
    @21
    cc
    wcel
    #
    @24
    @22
    wceq
    @5
    cpi
    cc
    wcel
    #
    @14
    cc
    wcel
    #
    @69
    picn
    @5
    @14
    @5
    @3
    @5
    @25
    @3
    cr
    wcel
    #
    @68
    @25
    cpi
    cr
    wcel
    #
    cpi
    cc0
    wne
    #
    @72
    pire
    cpi
    pire
    pipos
    gt0ne0ii
    #
    cA
    cpi
    redivcl
    mp3an23
    syl
    flcld
    #
    zcnd
    #
    cpi
    @14
    mulcl
    sylancr
    cA
    @21
    negsub
    syldan
    @5
    @23
    @16
    cA
    caddc
    @5
    @23
    @14
    cpi
    cmul
    co
    #
    cneg
    #
    @16
    @5
    @21
    @78
    @5
    @70
    @71
    @21
    @78
    wceq
    picn
    @77
    cpi
    @14
    mulcom
    sylancr
    negeqd
    @5
    @71
    @70
    @16
    @79
    wceq
    @77
    picn
    @14
    cpi
    mulneg1
    sylancl
    eqtr4d
    oveq2d
    3eqtr2d
    fveq2d
    fveq2d
    @0
    @2
    @15
    cz
    wcel
    @19
    @20
    wceq
    @5
    @14
    @76
    znegcld
    cA
    @15
    abssinper
    syldan
    @5
    @1
    cc0
    cabs
    @0
    @2
    simpr
    fveq2d
    3eqtrd
    abs0
    syl6eq
    @5
    @8
    @12
    cc0
    @5
    @8
    cc0
    @12
    clt
    wbr
    #
    @12
    cc0
    wne
    #
    @5
    @8
    @6
    cc0
    cpi
    cioo
    co
    wcel
    #
    @80
    @5
    @8
    @6
    cr
    wcel
    #
    @6
    cpi
    clt
    wbr
    #
    wa
    #
    @8
    wa
    #
    @82
    @5
    @85
    @8
    @5
    @83
    @84
    @5
    @25
    @26
    @83
    @68
    pirp
    cA
    cpi
    modcl
    sylancl
    #
    @5
    @25
    @26
    @84
    @68
    pirp
    cA
    cpi
    modlt
    sylancl
    jca
    biantrurd
    @82
    @83
    @8
    @84
    w3a
    #
    @86
    cc0
    cr
    wcel
    #
    @73
    @82
    @88
    wb
    #
    0re
    pire
    @89
    cc0
    cxr
    wcel
    cpi
    cxr
    wcel
    @90
    @73
    cc0
    rexr
    cpi
    rexr
    cc0
    cpi
    @6
    elioo2
    syl2an
    mp2an
    @83
    @8
    @84
    3anan32
    bitri
    syl6bbr
    @82
    cc0
    @11
    @12
    clt
    @6
    sinq12gt0
    #
    @82
    @11
    @82
    @6
    @6
    cc0
    cpi
    elioore
    resincld
    #
    @82
    cc0
    @11
    clt
    wbr
    #
    cc0
    @11
    cle
    wbr
    #
    @91
    @82
    @89
    @11
    cr
    wcel
    @93
    @94
    wi
    0re
    @92
    cc0
    @11
    ltle
    sylancr
    mpd
    absidd
    breqtrrd
    syl6bi
    @89
    @80
    @81
    0re
    cc0
    @12
    ltne
    mpan
    syl6
    necon2bd
    mpd
    @5
    @8
    @10
    @5
    cc0
    @6
    cle
    wbr
    #
    @8
    @10
    wo
    #
    @5
    @25
    @26
    @95
    @68
    pirp
    cA
    cpi
    modge0
    sylancl
    @5
    @89
    @83
    @95
    @96
    wb
    0re
    @87
    cc0
    @6
    leloe
    sylancr
    mpbid
    ord
    mpd
    eqcomd
    @5
    @25
    @26
    @7
    @4
    wb
    @68
    pirp
    cA
    cpi
    mod0
    sylancl
    mpbid
    @0
    @4
    @1
    @3
    cpi
    cmul
    co
    #
    csin
    cfv
    cc0
    @0
    @97
    cA
    csin
    @0
    @70
    @74
    @97
    cA
    wceq
    picn
    @75
    cA
    cpi
    divcan1
    mp3an23
    fveq2d
    @3
    sinkpi
    sylan9req
    impbida
end
