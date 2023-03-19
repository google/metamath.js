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
include "crp.mm"
include "wa.mm"
include "cr.mm"
include "cmo.mm"
include "pire.mm"
include "pipos.mm"
include "elrpii.mm"
include "c2.mm"
include "wne.mm"
include "cmul.mm"
include "2ne0.mm"
include "a1i.mm"
include "2cn.mm"
include "2re.mm"
include "ax-mp.mm"
include "id.mm"
include "adantr.mm"
include "ci.mm"
include "ce.mm"
include "cabs.mm"
include "c1.mm"
include "mulcld.mm"
include "caddc.mm"
include "ax-icn.mm"
include "mul12d.mm"
include "2timesd.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "efadd.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "cneg.mm"
include "cmin.mm"
include "sinval.mm"
include "sylan9req.mm"
include "wb.mm"
include "efcl.mm"
include "syl.mm"
include "negicn.mm"
include "subcld.mm"
include "2mulicn.mm"
include "2muline0.mm"
include "diveq0ad.mm"
include "mpbid.mm"
include "subeq0ad.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "negidi.mm"
include "oveq1i.mm"
include "adddird.mm"
include "syl5reqr.mm"
include "mul02d.mm"
include "ef0.mm"
include "3eqtrd.mm"
include "abs1.mm"
include "syl6eq.mm"
include "absefib.mm"
include "biimparc.mm"
include "ancoms.mm"
include "syl2an2r.mm"
include "mulre.mm"
include "4animp1.mm"
include "4an31.mm"
include "eel1111.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wo.mm"
include "w3a.mm"
include "cioo.mm"
include "modcld.mm"
include "recnd.mm"
include "sincld.mm"
include "cfl.mm"
include "cle.mm"
include "0re.mm"
include "ltleii.mm"
include "gt0ne0.mm"
include "3adant3.mm"
include "3com23.mm"
include "mp3an.mm"
include "redivcld.mm"
include "flcld.mm"
include "znegcld.mm"
include "wi.mm"
include "abssinper.mm"
include "eqcomd.mm"
include "ex.mm"
include "mpd.mm"
include "zcnd.mm"
include "negcld.mm"
include "recni.mm"
include "mulneg1d.mm"
include "mulcomd.mm"
include "negeqd.mm"
include "oveq2.mm"
include "ad3antrrr.mm"
include "4an4132.mm"
include "negsubd.mm"
include "modval.mm"
include "mpan2.mm"
include "abs0.mm"
include "adantl.mm"
include "abs00d.mm"
include "notnotb.mm"
include "bicomi.mm"
include "ltne.mm"
include "neneqd.mm"
include "expcom.mm"
include "mpi.mm"
include "con3i.mm"
include "sylbir.mm"
include "sinq12gt0.mm"
include "nsyl.mm"
include "cxr.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "notbii.mm"
include "sylib.mm"
include "3anan12.mm"
include "modlt.mm"
include "sylancr.mm"
include "jca.mm"
include "not12an2impnot1.mm"
include "modge0.mm"
include "leloe.mm"
include "biimp3a.mm"
include "idiALT.mm"
include "mp3an2i.mm"
include "pm2.53.mm"
include "imp.mm"
include "mod0.mm"
include "3com12.mm"
include "divcan1d.mm"
include "sinkpi.mm"
include "impbid.mm"

theorem sineq0ALT
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
    @4
    cpi
    crp
    wcel
    #
    @0
    @2
    wa
    #
    cA
    cr
    wcel
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
    cpi
    pire
    pipos
    elrpii
    #
    @6
    c2
    cc0
    wne
    #
    c2
    cr
    wcel
    #
    @0
    c2
    cA
    cmul
    co
    #
    cr
    wcel
    #
    @7
    @11
    @6
    2ne0
    a1i
    @12
    @6
    c2
    cc
    wcel
    #
    @12
    2cn
    @12
    @15
    2re
    a1i
    ax-mp
    a1i
    @0
    @0
    @2
    @0
    id
    #
    adantr
    #
    @0
    @13
    cc
    wcel
    #
    @2
    ci
    @13
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
    wceq
    #
    @14
    @0
    c2
    cA
    @15
    @0
    2cn
    a1i
    #
    @16
    mulcld
    @6
    @21
    c1
    cabs
    cfv
    c1
    @6
    @20
    c1
    cabs
    @6
    @20
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    @25
    cmul
    co
    #
    c1
    @0
    @20
    @26
    wceq
    @2
    @0
    @20
    @24
    @24
    caddc
    co
    #
    ce
    cfv
    #
    @26
    @0
    @19
    @27
    ce
    @0
    c2
    @24
    cmul
    co
    @19
    @27
    @0
    c2
    ci
    cA
    @23
    ci
    cc
    wcel
    @0
    ax-icn
    a1i
    #
    @16
    mul12d
    @0
    @24
    @0
    ci
    cA
    @29
    @16
    mulcld
    #
    2timesd
    eqtr3d
    fveq2d
    @0
    @24
    cc
    wcel
    #
    @31
    @28
    @26
    wceq
    @30
    @30
    @24
    @24
    efadd
    syl2anc
    eqtrd
    adantr
    @6
    @26
    @24
    ci
    cneg
    #
    cA
    cmul
    co
    #
    caddc
    co
    #
    ce
    cfv
    #
    cc0
    ce
    cfv
    #
    c1
    @6
    @26
    @25
    @33
    ce
    cfv
    #
    cmul
    co
    #
    @35
    @6
    @25
    @37
    @25
    cmul
    @6
    @25
    @37
    cmin
    co
    #
    cc0
    wceq
    #
    @25
    @37
    wceq
    #
    @6
    @39
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
    @40
    @0
    @2
    @43
    @1
    cc0
    cA
    sinval
    @2
    id
    #
    sylan9req
    @0
    @44
    @40
    wb
    @2
    @0
    @39
    @42
    @0
    @25
    @37
    @0
    @31
    @25
    cc
    wcel
    @30
    @24
    efcl
    syl
    #
    @0
    @33
    cc
    wcel
    #
    @37
    cc
    wcel
    @0
    @32
    cA
    @32
    cc
    wcel
    @0
    negicn
    a1i
    #
    @16
    mulcld
    #
    @33
    efcl
    syl
    #
    subcld
    @42
    cc
    wcel
    @0
    2mulicn
    a1i
    @42
    cc0
    wne
    @0
    2muline0
    a1i
    diveq0ad
    adantr
    mpbid
    @0
    @40
    @41
    wb
    @2
    @0
    @25
    @37
    @46
    @50
    subeq0ad
    adantr
    mpbid
    oveq2d
    @0
    @35
    @38
    wceq
    #
    @2
    @0
    @31
    @47
    @51
    @30
    @49
    @24
    @33
    efadd
    syl2anc
    adantr
    eqtr4d
    @0
    @35
    @36
    wceq
    @2
    @0
    @34
    cc0
    ce
    @0
    @34
    cc0
    cA
    cmul
    co
    #
    cc0
    @0
    @52
    ci
    @32
    caddc
    co
    #
    cA
    cmul
    co
    @34
    @53
    cc0
    cA
    cmul
    ci
    ax-icn
    negidi
    oveq1i
    @0
    ci
    @32
    cA
    @29
    @48
    @16
    adddird
    syl5reqr
    @0
    cA
    @16
    mul02d
    eqtrd
    fveq2d
    adantr
    @36
    c1
    wceq
    @6
    ef0
    a1i
    3eqtrd
    eqtrd
    fveq2d
    abs1
    syl6eq
    @22
    @18
    @14
    @18
    @14
    @22
    @13
    absefib
    biimparc
    ancoms
    syl2an2r
    @11
    @12
    @0
    @14
    @7
    @0
    @12
    @11
    @14
    @7
    cA
    c2
    mulre
    4animp1
    4an31
    eel1111
    #
    @6
    cc0
    @8
    @6
    cc0
    @8
    clt
    wbr
    #
    wn
    #
    @55
    cc0
    @8
    wceq
    #
    wo
    #
    @57
    @6
    @55
    @8
    cr
    wcel
    #
    @8
    cpi
    clt
    wbr
    #
    wa
    #
    wa
    #
    wn
    #
    @61
    @56
    @6
    @59
    @55
    @60
    w3a
    #
    wn
    #
    @63
    @6
    @8
    cc0
    cpi
    cioo
    co
    wcel
    #
    wn
    @65
    @6
    cc0
    @8
    csin
    cfv
    #
    clt
    wbr
    #
    @66
    @6
    @67
    cc0
    wceq
    #
    @68
    wn
    #
    @6
    @67
    @6
    @8
    @6
    @8
    @6
    cA
    cpi
    @54
    @5
    @6
    @10
    a1i
    modcld
    #
    recnd
    sincld
    @6
    @1
    cabs
    cfv
    #
    @67
    cabs
    cfv
    #
    cc0
    @6
    @72
    cA
    cpi
    @3
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    csin
    cfv
    #
    cabs
    cfv
    #
    @73
    @6
    @72
    cA
    @74
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
    @78
    @6
    @79
    cz
    wcel
    #
    @72
    @83
    wceq
    #
    @6
    @74
    @6
    @3
    @6
    cA
    cpi
    @54
    cpi
    cr
    wcel
    #
    @6
    pire
    a1i
    cpi
    cc0
    wne
    #
    @6
    @86
    cc0
    cpi
    cle
    wbr
    #
    cc0
    cpi
    clt
    wbr
    #
    @87
    pire
    cc0
    cpi
    0re
    pire
    pipos
    ltleii
    pipos
    @86
    @89
    @88
    @87
    @86
    @89
    @87
    @88
    cpi
    gt0ne0
    3adant3
    3com23
    mp3an
    #
    a1i
    redivcld
    flcld
    #
    znegcld
    @0
    @84
    @85
    wi
    @2
    @0
    @84
    @85
    @0
    @84
    wa
    @83
    @72
    cA
    @79
    abssinper
    eqcomd
    ex
    adantr
    mpd
    @6
    @82
    @77
    cabs
    @6
    @81
    @76
    csin
    @6
    @81
    cA
    @75
    cneg
    #
    caddc
    co
    #
    @76
    @6
    @0
    @80
    cc
    wcel
    #
    @92
    cc
    wcel
    #
    @80
    @92
    wceq
    #
    @81
    @93
    wceq
    #
    @17
    @6
    @79
    cpi
    @6
    @74
    @6
    @74
    @91
    zcnd
    #
    negcld
    cpi
    cc
    wcel
    #
    @6
    cpi
    pire
    recni
    #
    a1i
    #
    mulcld
    @6
    @75
    @6
    cpi
    @74
    @101
    @98
    mulcld
    #
    negcld
    @6
    @80
    @74
    cpi
    cmul
    co
    #
    cneg
    @92
    @6
    @74
    cpi
    @98
    @101
    mulneg1d
    @6
    @103
    @75
    @6
    @74
    cpi
    @98
    @101
    mulcomd
    negeqd
    eqtrd
    @0
    @94
    @95
    @96
    @97
    @96
    @97
    @95
    @94
    @0
    @80
    @92
    cA
    caddc
    oveq2
    ad3antrrr
    4an4132
    eel1111
    @6
    cA
    @75
    @17
    @102
    negsubd
    eqtrd
    fveq2d
    fveq2d
    eqtrd
    @6
    @7
    @73
    @78
    wceq
    #
    @54
    @7
    @5
    @104
    @10
    @7
    @5
    wa
    #
    @67
    @77
    cabs
    @105
    @8
    @76
    csin
    cA
    cpi
    modval
    fveq2d
    fveq2d
    mpan2
    syl
    eqtr4d
    @2
    @72
    cc0
    wceq
    @0
    @2
    @72
    cc0
    cabs
    cfv
    cc0
    @2
    @1
    cc0
    cabs
    @45
    fveq2d
    abs0
    syl6eq
    adantl
    eqtr3d
    abs00d
    @69
    @69
    wn
    #
    wn
    #
    @70
    @69
    @107
    @69
    notnotb
    bicomi
    @68
    @106
    @68
    cc0
    cr
    wcel
    #
    @106
    0re
    @108
    @68
    @106
    @108
    @68
    wa
    @67
    cc0
    cc0
    @67
    ltne
    neneqd
    expcom
    mpi
    con3i
    sylbir
    syl
    @8
    sinq12gt0
    nsyl
    @66
    @64
    cc0
    cxr
    wcel
    cpi
    cxr
    wcel
    @66
    @64
    wb
    cc0
    0re
    rexri
    cpi
    pire
    rexri
    cc0
    cpi
    @8
    elioo2
    mp2an
    notbii
    sylib
    @64
    @62
    @59
    @55
    @60
    3anan12
    notbii
    sylib
    @6
    @59
    @60
    @71
    @6
    @5
    @7
    @60
    @10
    @54
    @7
    @5
    @60
    cA
    cpi
    modlt
    ancoms
    sylancr
    jca
    @55
    @61
    not12an2impnot1
    syl2anc
    @108
    @6
    @59
    cc0
    @8
    cle
    wbr
    #
    @58
    0re
    @71
    @6
    @5
    @7
    @109
    @10
    @54
    @7
    @5
    @109
    cA
    cpi
    modge0
    ancoms
    sylancr
    @108
    @59
    @109
    w3a
    @58
    wi
    @108
    @59
    @109
    @58
    cc0
    @8
    leloe
    biimp3a
    idiALT
    mp3an2i
    @58
    @56
    @57
    @58
    @56
    @57
    @55
    @57
    pm2.53
    imp
    ancoms
    syl2anc
    eqcomd
    @7
    @5
    @9
    @4
    @7
    @5
    @9
    @4
    cA
    cpi
    mod0
    biimp3a
    3com12
    mp3an2i
    ex
    @0
    @4
    @2
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
    #
    cc0
    @0
    @110
    cA
    csin
    @0
    cA
    cpi
    @16
    @99
    @0
    @100
    a1i
    @87
    @0
    @90
    a1i
    divcan1d
    fveq2d
    @4
    @4
    @111
    cc0
    wceq
    @4
    id
    @3
    sinkpi
    syl
    sylan9req
    ex
    impbid
end
