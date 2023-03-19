include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cn.mm"
include "w3a.mm"
include "cexp.mm"
include "cmo.mm"
include "cfl.mm"
include "cfv.mm"
include "clt.mm"
include "cr.mm"
include "zre.mm"
include "3ad2ant1.mm"
include "crp.mm"
include "2rp.mm"
include "a1i.mm"
include "nnz.mm"
include "rpexpcld.mm"
include "rpred.mm"
include "3ad2ant3.mm"
include "resubcld.mm"
include "modcld.mm"
include "peano2zm.mm"
include "zred.mm"
include "caddc.mm"
include "1red.mm"
include "readdcld.mm"
include "wbr.mm"
include "cneg.mm"
include "cc0.mm"
include "wceq.mm"
include "cif.mm"
include "wa.mm"
include "2nn.mm"
include "nnnn0.mm"
include "nnexpcld.mm"
include "anim2i.mm"
include "3adant2.mm"
include "m1modmmod.mm"
include "syl.mm"
include "wne.mm"
include "wi.mm"
include "cc.mm"
include "zcn.mm"
include "xp1d2m1eqxm1d2.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eleq1d.mm"
include "peano2z.mm"
include "1cnd.mm"
include "addcld.mm"
include "halfcld.mm"
include "npcand.mm"
include "syl5ib.mm"
include "sylbid.mm"
include "wn.mm"
include "wb.mm"
include "mod0.mm"
include "syl2an.mm"
include "cmul.mm"
include "cn0.mm"
include "nnzd.mm"
include "nnm1nn0.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "adantl.mm"
include "simpr.mm"
include "zmulcld.mm"
include "ex.mm"
include "zcnd.mm"
include "negsubd.mm"
include "oveq1d.mm"
include "negcld.mm"
include "pncan2d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "2cnd.mm"
include "2ne0.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "jca.mm"
include "expsub.mm"
include "syl21anc.mm"
include "expn1.mm"
include "3eqtr3d.mm"
include "expcld.mm"
include "rpcnne0d.mm"
include "div12.mm"
include "syl3anc.mm"
include "divrecd.mm"
include "3eqtr4d.mm"
include "sylibd.mm"
include "zeo2.mm"
include "necon2ad.mm"
include "3syld.mm"
include "com23.mm"
include "3imp.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "neg1lt0.mm"
include "2re.mm"
include "1lt2.mm"
include "expgt1.mm"
include "mp3an13.mm"
include "posdifd.mm"
include "mpbid.mm"
include "renegcld.mm"
include "0red.mm"
include "lttr.mm"
include "mpan2d.mm"
include "mpi.mm"
include "eqbrtrd.mm"
include "ltsubadd2b.mm"
include "syl22anc.mm"
include "modid0.mm"
include "recnd.mm"
include "subid1d.mm"
include "modsubmodmod.mm"
include "modabs2.mm"
include "breqtrrd.mm"
include "ltsub2dd.mm"
include "subsub4d.mm"
include "3brtr4d.mm"
include "ltdiv1dd.mm"
include "expne0d.mm"
include "divsub1dir.mm"
include "fveq2d.mm"
include "fldivmod.mm"

theorem dignn0flhalflem1
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ZZ /\ ( ( A - 1 ) / 2 ) e. NN /\ N e. NN ) -> ( |_ ` ( ( A / ( 2 ^ N ) ) - 1 ) ) < ( |_ ` ( ( A - 1 ) / ( 2 ^ N ) ) ) )

  proof
    cA
    cz
    wcel
    #
    cA
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cA
    c2
    cN
    cexp
    co
    #
    cmin
    co
    #
    @7
    @6
    cmo
    co
    #
    cmin
    co
    #
    @6
    cdiv
    co
    #
    @1
    @1
    @6
    cmo
    co
    #
    cmin
    co
    #
    @6
    cdiv
    co
    #
    cA
    @6
    cdiv
    co
    #
    c1
    cmin
    co
    #
    cfl
    cfv
    #
    @1
    @6
    cdiv
    co
    cfl
    cfv
    #
    clt
    @5
    @9
    @12
    @6
    @5
    @7
    @8
    @5
    cA
    @6
    @0
    @3
    cA
    cr
    wcel
    #
    @4
    cA
    zre
    #
    3ad2ant1
    #
    @4
    @0
    @6
    cr
    wcel
    #
    @3
    @4
    @6
    @4
    c2
    cN
    c2
    crp
    wcel
    #
    @4
    2rp
    a1i
    cN
    nnz
    #
    rpexpcld
    #
    rpred
    #
    3ad2ant3
    #
    resubcld
    #
    @5
    @7
    @6
    @27
    @4
    @0
    @6
    crp
    wcel
    #
    @3
    @24
    3ad2ant3
    #
    modcld
    #
    resubcld
    @5
    @1
    @11
    @0
    @3
    @1
    cr
    wcel
    #
    @4
    @0
    @1
    cA
    peano2zm
    zred
    3ad2ant1
    #
    @5
    @1
    @6
    @32
    @29
    modcld
    #
    resubcld
    @29
    @5
    cA
    @6
    @8
    caddc
    co
    #
    cmin
    co
    cA
    c1
    @11
    caddc
    co
    #
    cmin
    co
    @9
    @12
    clt
    @5
    @35
    @34
    cA
    @5
    c1
    @11
    @5
    1red
    #
    @33
    readdcld
    @5
    @6
    @8
    @26
    @30
    readdcld
    @20
    @5
    @35
    @6
    cA
    @6
    cmo
    co
    #
    caddc
    co
    #
    @34
    clt
    @5
    @11
    @37
    cmin
    co
    #
    @6
    c1
    cmin
    co
    #
    clt
    wbr
    #
    @35
    @38
    clt
    wbr
    #
    @5
    @39
    c1
    cneg
    #
    @40
    clt
    @5
    @39
    @37
    cc0
    wceq
    #
    @40
    @43
    cif
    #
    @43
    @5
    @0
    @6
    cn
    wcel
    #
    wa
    #
    @39
    @45
    wceq
    @0
    @4
    @47
    @3
    @4
    @46
    @0
    @4
    c2
    cN
    c2
    cn
    wcel
    @4
    2nn
    a1i
    #
    cN
    nnnn0
    nnexpcld
    anim2i
    3adant2
    cA
    @6
    m1modmmod
    syl
    @5
    @44
    @40
    @43
    @5
    @37
    cc0
    @0
    @3
    @4
    @37
    cc0
    wne
    #
    @0
    @4
    @3
    @49
    @0
    @4
    @3
    @49
    wi
    @0
    @4
    wa
    #
    @3
    @2
    cz
    wcel
    #
    cA
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @49
    @3
    @51
    wi
    @50
    @2
    nnz
    a1i
    @50
    @51
    @53
    c1
    cmin
    co
    #
    cz
    wcel
    #
    @54
    @50
    @2
    @55
    cz
    @0
    @2
    @55
    wceq
    #
    @4
    @0
    cA
    cc
    wcel
    #
    @57
    cA
    zcn
    #
    @58
    @55
    @2
    cA
    xp1d2m1eqxm1d2
    eqcomd
    syl
    adantr
    eleq1d
    @56
    @55
    c1
    caddc
    co
    #
    cz
    wcel
    @50
    @54
    @55
    peano2z
    @50
    @60
    @53
    cz
    @50
    @53
    c1
    @50
    @52
    @50
    cA
    c1
    @0
    @58
    @4
    @59
    adantr
    #
    @50
    1cnd
    #
    addcld
    halfcld
    @62
    npcand
    eleq1d
    syl5ib
    sylbid
    @50
    @54
    @37
    cc0
    @50
    @44
    cA
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @54
    wn
    #
    @50
    @44
    @14
    cz
    wcel
    #
    @64
    @0
    @18
    @28
    @44
    @66
    wb
    @4
    @19
    @24
    cA
    @6
    mod0
    syl2an
    @50
    @66
    c2
    cN
    c1
    cmin
    co
    #
    cexp
    co
    #
    @14
    cmul
    co
    #
    cz
    wcel
    #
    @64
    @50
    @66
    @70
    @50
    @66
    wa
    @68
    @14
    @50
    @68
    cz
    wcel
    #
    @66
    @4
    @71
    @0
    @4
    c2
    cz
    wcel
    @67
    cn0
    wcel
    @71
    @4
    c2
    @48
    nnzd
    cN
    nnm1nn0
    #
    c2
    @67
    zexpcl
    syl2anc
    adantl
    adantr
    @50
    @66
    simpr
    zmulcld
    ex
    @50
    @69
    @63
    cz
    @50
    cA
    @68
    @6
    cdiv
    co
    #
    cmul
    co
    #
    cA
    c1
    c2
    cdiv
    co
    #
    cmul
    co
    @69
    @63
    @50
    @73
    @75
    cA
    cmul
    @50
    c2
    @67
    cN
    cmin
    co
    #
    cexp
    co
    #
    c2
    @43
    cexp
    co
    #
    @73
    @75
    @50
    @76
    @43
    c2
    cexp
    @50
    @76
    cN
    @43
    caddc
    co
    #
    cN
    cmin
    co
    @43
    @50
    @67
    @79
    cN
    cmin
    @50
    @79
    @67
    @50
    cN
    c1
    @50
    cN
    @4
    cN
    cz
    wcel
    #
    @0
    @23
    adantl
    #
    zcnd
    #
    @62
    negsubd
    eqcomd
    oveq1d
    @50
    cN
    @43
    @82
    @50
    c1
    @62
    negcld
    pncan2d
    eqtrd
    oveq2d
    @50
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @67
    cz
    wcel
    #
    @80
    wa
    #
    @77
    @73
    wceq
    @50
    2cnd
    #
    @84
    @50
    2ne0
    a1i
    #
    @4
    @86
    @0
    @4
    @85
    @80
    @4
    cN
    c1
    @23
    @4
    1zzd
    zsubcld
    @23
    jca
    adantl
    c2
    @67
    cN
    expsub
    syl21anc
    @50
    @83
    @78
    @75
    wceq
    @87
    c2
    expn1
    syl
    3eqtr3d
    oveq2d
    @50
    @68
    cc
    wcel
    #
    @58
    @6
    cc
    wcel
    #
    @6
    cc0
    wne
    #
    wa
    @69
    @74
    wceq
    @4
    @89
    @0
    @4
    c2
    @67
    @4
    2cnd
    #
    @72
    expcld
    adantl
    @61
    @50
    @6
    @50
    c2
    cN
    @22
    @50
    2rp
    a1i
    @81
    rpexpcld
    rpcnne0d
    @68
    cA
    @6
    div12
    syl3anc
    @50
    cA
    c2
    @61
    @87
    @88
    divrecd
    3eqtr4d
    eleq1d
    sylibd
    sylbid
    @0
    @64
    @65
    wb
    @4
    cA
    zeo2
    adantr
    sylibd
    necon2ad
    3syld
    ex
    com23
    3imp
    neneqd
    iffalsed
    eqtrd
    @4
    @0
    @43
    @40
    clt
    wbr
    #
    @3
    @4
    @43
    cc0
    clt
    wbr
    #
    @93
    neg1lt0
    @4
    @94
    cc0
    @40
    clt
    wbr
    #
    @93
    @4
    c1
    @6
    clt
    wbr
    #
    @95
    c2
    cr
    wcel
    @4
    c1
    c2
    clt
    wbr
    @96
    2re
    1lt2
    c2
    cN
    expgt1
    mp3an13
    @4
    c1
    @6
    @4
    1red
    #
    @25
    posdifd
    mpbid
    @4
    @43
    cr
    wcel
    cc0
    cr
    wcel
    @40
    cr
    wcel
    @94
    @95
    wa
    @93
    wi
    @4
    c1
    @97
    renegcld
    @4
    0red
    @4
    @6
    c1
    @25
    @97
    resubcld
    @43
    cc0
    @40
    lttr
    syl3anc
    mpan2d
    mpi
    3ad2ant3
    eqbrtrd
    @5
    c1
    cr
    wcel
    @21
    @37
    cr
    wcel
    @11
    cr
    wcel
    @41
    @42
    wb
    @36
    @26
    @5
    cA
    @6
    @20
    @29
    modcld
    #
    @33
    c1
    @6
    @37
    @11
    ltsubadd2b
    syl22anc
    mpbid
    @5
    @8
    @37
    @6
    caddc
    @5
    @37
    @6
    @6
    cmo
    co
    #
    cmin
    co
    #
    @6
    cmo
    co
    #
    @37
    @6
    cmo
    co
    #
    @8
    @37
    @5
    @100
    @37
    @6
    cmo
    @5
    @100
    @37
    cc0
    cmin
    co
    @37
    @5
    @99
    cc0
    @37
    cmin
    @5
    @28
    @99
    cc0
    wceq
    @29
    @6
    modid0
    syl
    oveq2d
    @5
    @37
    @5
    @37
    @98
    recnd
    subid1d
    eqtrd
    oveq1d
    @5
    @18
    @21
    @28
    @101
    @8
    wceq
    @20
    @26
    @29
    cA
    @6
    @6
    modsubmodmod
    syl3anc
    @5
    @18
    @28
    @102
    @37
    wceq
    @20
    @29
    cA
    @6
    modabs2
    syl2anc
    3eqtr3d
    oveq2d
    breqtrrd
    ltsub2dd
    @5
    cA
    @6
    @8
    @0
    @3
    @58
    @4
    @59
    3ad2ant1
    #
    @5
    @6
    @26
    recnd
    @5
    @8
    @30
    recnd
    subsub4d
    @5
    cA
    c1
    @11
    @103
    @5
    1cnd
    @5
    @11
    @33
    recnd
    subsub4d
    3brtr4d
    ltdiv1dd
    @5
    @16
    @7
    @6
    cdiv
    co
    #
    cfl
    cfv
    #
    @10
    @5
    @58
    @90
    @91
    @16
    @105
    wceq
    @103
    @4
    @0
    @90
    @3
    @4
    @6
    @25
    recnd
    3ad2ant3
    @4
    @0
    @91
    @3
    @4
    c2
    cN
    @92
    @84
    @4
    2ne0
    a1i
    @23
    expne0d
    3ad2ant3
    @58
    @90
    @91
    w3a
    @15
    @104
    cfl
    cA
    @6
    divsub1dir
    fveq2d
    syl3anc
    @5
    @7
    cr
    wcel
    @28
    @105
    @10
    wceq
    @27
    @29
    @7
    @6
    fldivmod
    syl2anc
    eqtrd
    @5
    @31
    @28
    @17
    @13
    wceq
    @32
    @29
    @1
    @6
    fldivmod
    syl2anc
    3brtr4d
end
