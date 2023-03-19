include "c2.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "cppi.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "c8.mm"
include "c1.mm"
include "ceu.mm"
include "cmul.mm"
include "cmin.mm"
include "cr.mm"
include "wss.mm"
include "cxr.mm"
include "2re.mm"
include "pnfxr.mm"
include "icossre.mm"
include "mp2an.mm"
include "a1i.mm"
include "cc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "elicopnf.mm"
include "ax-mp.mm"
include "simplbi.mm"
include "cc0.mm"
include "0red.mm"
include "1re.mm"
include "clt.mm"
include "0lt1.mm"
include "1lt2.mm"
include "simprbi.mm"
include "ltletrd.mm"
include "lttrd.mm"
include "elrpd.mm"
include "rplogcld.mm"
include "rpdivcld.mm"
include "cn.mm"
include "ppinncl.mm"
include "sylbi.mm"
include "nnrpd.mm"
include "rpcnd.mm"
include "adantl.mm"
include "8re.mm"
include "crp.mm"
include "2rp.mm"
include "relogcl.mm"
include "ere.mm"
include "remulcli.mm"
include "2pos.mm"
include "epos.mm"
include "mulgt0ii.mm"
include "gt0ne0ii.mm"
include "rereccli.mm"
include "resubcli.mm"
include "2t1e2.mm"
include "c3.mm"
include "egt2lt3.mm"
include "simpli.mm"
include "lttri.mm"
include "ltmul2i.mm"
include "mpbi.mm"
include "eqbrtrri.mm"
include "ltrecii.mm"
include "c4.mm"
include "simpri.mm"
include "3lt4.mm"
include "3re.mm"
include "4re.mm"
include "epr.mm"
include "4pos.mm"
include "elrpii.mm"
include "logltb.mm"
include "loge.mm"
include "cexp.mm"
include "sq2.mm"
include "fveq2i.mm"
include "cz.mm"
include "wceq.mm"
include "2z.mm"
include "relogexp.mm"
include "eqtr3i.mm"
include "3brtr3i.mm"
include "pm3.2i.mm"
include "ltdivmul.mm"
include "mp3an.mm"
include "mpbir.mm"
include "halfre.mm"
include "posdifi.mm"
include "rerpdivcl.mm"
include "cabs.mm"
include "rpre.mm"
include "rpge0.mm"
include "absidd.mm"
include "syl.mm"
include "adantr.mm"
include "cfl.mm"
include "eqid.mm"
include "chebbnd1lem3.mm"
include "sylan.mm"
include "wne.mm"
include "recni.mm"
include "2ne0.mm"
include "recdiv.mm"
include "mp4an.mm"
include "nncnd.mm"
include "rpne0d.mm"
include "nnne0d.mm"
include "recdivd.mm"
include "divrecd.mm"
include "rpcnne0d.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "3brtr4d.mm"
include "elrp.mm"
include "divgt0ii.mm"
include "ltrec.mm"
include "mpanr12.mm"
include "mpbird.mm"
include "wi.mm"
include "rpred.mm"
include "ltle.mm"
include "sylancl.mm"
include "mpd.mm"
include "eqbrtrd.mm"
include "elo1d.mm"
include "trud.mm"

theorem chebbnd1
  let vx: setvar x


  assert |- ( x e. ( 2 [,) +oo ) |-> ( ( x / ( log ` x ) ) / ( ppi ` x ) ) ) e. O(1)

  proof
    vx
    c2
    cpnf
    cico
    co
    #
    vx
    cv
    #
    @1
    clog
    cfv
    #
    cdiv
    co
    #
    @1
    cppi
    cfv
    #
    cdiv
    co
    #
    cmpt
    co1
    wcel
    wtru
    vx
    @0
    @5
    c8
    c2
    c2
    clog
    cfv
    #
    c1
    c2
    ceu
    cmul
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    cdiv
    co
    #
    @0
    cr
    wss
    #
    wtru
    c2
    cr
    wcel
    #
    cpnf
    cxr
    wcel
    @11
    2re
    pnfxr
    c2
    cpnf
    icossre
    mp2an
    a1i
    @1
    @0
    wcel
    #
    @5
    cc
    wcel
    wtru
    @13
    @5
    @13
    @3
    @4
    @13
    @1
    @2
    @13
    @1
    @13
    @1
    cr
    wcel
    #
    c2
    @1
    cle
    wbr
    #
    @12
    @13
    @14
    @15
    wa
    #
    wb
    2re
    c2
    @1
    elicopnf
    ax-mp
    #
    simplbi
    #
    @13
    cc0
    c1
    @1
    @13
    0red
    c1
    cr
    wcel
    #
    @13
    1re
    a1i
    #
    @18
    cc0
    c1
    clt
    wbr
    @13
    0lt1
    a1i
    @13
    c1
    c2
    @1
    @20
    @12
    @13
    2re
    a1i
    @18
    c1
    c2
    clt
    wbr
    #
    @13
    1lt2
    a1i
    @13
    @14
    @15
    @17
    simprbi
    ltletrd
    #
    lttrd
    elrpd
    #
    @13
    @1
    @18
    @22
    rplogcld
    #
    rpdivcld
    #
    @13
    @4
    @13
    @16
    @4
    cn
    wcel
    @17
    @1
    ppinncl
    sylbi
    #
    nnrpd
    rpdivcld
    #
    rpcnd
    adantl
    c8
    cr
    wcel
    wtru
    8re
    a1i
    @10
    cr
    wcel
    #
    wtru
    @12
    @9
    crp
    wcel
    @28
    2re
    @9
    @6
    @8
    c2
    crp
    wcel
    #
    @6
    cr
    wcel
    #
    2rp
    c2
    relogcl
    ax-mp
    #
    @7
    c2
    ceu
    2re
    ere
    remulcli
    #
    @7
    @32
    c2
    ceu
    2re
    ere
    2pos
    epos
    mulgt0ii
    #
    gt0ne0ii
    rereccli
    #
    resubcli
    #
    @8
    @6
    clt
    wbr
    #
    cc0
    @9
    clt
    wbr
    @8
    c1
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @37
    @6
    clt
    wbr
    #
    @36
    c2
    @7
    clt
    wbr
    @38
    c2
    c1
    cmul
    co
    #
    c2
    @7
    clt
    2t1e2
    c1
    ceu
    clt
    wbr
    #
    @40
    @7
    clt
    wbr
    #
    @21
    c2
    ceu
    clt
    wbr
    #
    @41
    1lt2
    @43
    ceu
    c3
    clt
    wbr
    #
    egt2lt3
    simpli
    c1
    c2
    ceu
    1re
    2re
    ere
    lttri
    mp2an
    cc0
    c2
    clt
    wbr
    #
    @41
    @42
    wb
    2pos
    c1
    ceu
    c2
    1re
    ere
    2re
    ltmul2i
    ax-mp
    mpbi
    eqbrtrri
    c2
    @7
    2re
    @32
    2pos
    @33
    ltrecii
    mpbi
    @39
    c1
    c2
    @6
    cmul
    co
    #
    clt
    wbr
    #
    ceu
    clog
    cfv
    #
    c4
    clog
    cfv
    #
    c1
    @46
    clt
    ceu
    c4
    clt
    wbr
    #
    @48
    @49
    clt
    wbr
    #
    @44
    c3
    c4
    clt
    wbr
    @50
    @43
    @44
    egt2lt3
    simpri
    3lt4
    ceu
    c3
    c4
    ere
    3re
    4re
    lttri
    mp2an
    ceu
    crp
    wcel
    c4
    crp
    wcel
    @50
    @51
    wb
    epr
    c4
    4re
    4pos
    elrpii
    ceu
    c4
    logltb
    mp2an
    mpbi
    loge
    c2
    c2
    cexp
    co
    #
    clog
    cfv
    #
    @49
    @46
    @52
    c4
    clog
    sq2
    fveq2i
    @29
    c2
    cz
    wcel
    @53
    @46
    wceq
    2rp
    2z
    c2
    c2
    relogexp
    mp2an
    eqtr3i
    3brtr3i
    @19
    @30
    @12
    @45
    wa
    @39
    @47
    wb
    1re
    @31
    @12
    @45
    2re
    2pos
    pm3.2i
    c1
    @6
    c2
    ltdivmul
    mp3an
    mpbir
    @8
    @37
    @6
    @34
    halfre
    @31
    lttri
    mp2an
    @8
    @6
    @34
    @31
    posdifi
    mpbi
    #
    elrpii
    c2
    @9
    rerpdivcl
    mp2an
    #
    a1i
    @13
    c8
    @1
    cle
    wbr
    #
    wa
    #
    @5
    cabs
    cfv
    #
    @10
    cle
    wbr
    wtru
    @57
    @58
    @5
    @10
    cle
    @13
    @58
    @5
    wceq
    #
    @56
    @13
    @5
    crp
    wcel
    #
    @59
    @27
    @60
    @5
    @5
    rpre
    @5
    rpge0
    absidd
    syl
    adantr
    @57
    @5
    @10
    clt
    wbr
    #
    @5
    @10
    cle
    wbr
    #
    @57
    @61
    c1
    @10
    cdiv
    co
    #
    c1
    @5
    cdiv
    co
    #
    clt
    wbr
    #
    @57
    @9
    c2
    cdiv
    co
    #
    @4
    @2
    @1
    cdiv
    co
    #
    cmul
    co
    #
    @63
    @64
    clt
    @13
    @14
    @56
    @66
    @68
    clt
    wbr
    @18
    @1
    c2
    cdiv
    co
    cfl
    cfv
    #
    @1
    @69
    eqid
    chebbnd1lem3
    sylan
    @63
    @66
    wceq
    #
    @57
    c2
    cc
    wcel
    c2
    cc0
    wne
    @9
    cc
    wcel
    @9
    cc0
    wne
    @70
    c2
    2re
    recni
    2ne0
    @9
    @35
    recni
    @9
    @35
    @54
    gt0ne0ii
    c2
    @9
    recdiv
    mp4an
    a1i
    @13
    @64
    @68
    wceq
    @56
    @13
    @64
    @4
    @3
    cdiv
    co
    @4
    c1
    @3
    cdiv
    co
    #
    cmul
    co
    @68
    @13
    @3
    @4
    @13
    @3
    @25
    rpcnd
    #
    @13
    @4
    @26
    nncnd
    #
    @13
    @3
    @25
    rpne0d
    #
    @13
    @4
    @26
    nnne0d
    recdivd
    @13
    @4
    @3
    @73
    @72
    @74
    divrecd
    @13
    @71
    @67
    @4
    cmul
    @13
    @1
    cc
    wcel
    @1
    cc0
    wne
    wa
    @2
    cc
    wcel
    @2
    cc0
    wne
    wa
    @71
    @67
    wceq
    @13
    @1
    @23
    rpcnne0d
    @13
    @2
    @24
    rpcnne0d
    @1
    @2
    recdiv
    syl2anc
    oveq2d
    3eqtrd
    adantr
    3brtr4d
    @57
    @60
    @61
    @65
    wb
    #
    @13
    @60
    @56
    @27
    adantr
    #
    @60
    @5
    cr
    wcel
    #
    cc0
    @5
    clt
    wbr
    wa
    #
    @75
    @5
    elrp
    @78
    @28
    cc0
    @10
    clt
    wbr
    @75
    @55
    c2
    @9
    2re
    @35
    2pos
    @54
    divgt0ii
    @5
    @10
    ltrec
    mpanr12
    sylbi
    syl
    mpbird
    @57
    @77
    @28
    @61
    @62
    wi
    @57
    @5
    @76
    rpred
    @55
    @5
    @10
    ltle
    sylancl
    mpd
    eqbrtrd
    adantl
    elo1d
    trud
end
