include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "cv.mm"
include "cmul.mm"
include "wrex.mm"
include "wi.mm"
include "wb.mm"
include "evennn2n.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "2cnd.mm"
include "nncn.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "cn0.mm"
include "2nn0.mm"
include "a1i.mm"
include "nnnn0.mm"
include "expmuld.mm"
include "eqtrd.mm"
include "adantl.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "cuz.mm"
include "cfv.mm"
include "wo.mm"
include "elnn1uz2.mm"
include "c3.mm"
include "cc.mm"
include "2cn.mm"
include "exp1.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "c4.mm"
include "sq2.mm"
include "oveq1i.mm"
include "4m1e3.mm"
include "eqtri.mm"
include "adantr.mm"
include "cle.mm"
include "eqcom.mm"
include "cr.mm"
include "eldifi.mm"
include "prmnn.mm"
include "nnre.mm"
include "3syl.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "reexpcld.mm"
include "simpr.mm"
include "eqled.mm"
include "ex.mm"
include "syl5bi.mm"
include "clog.mm"
include "cdiv.mm"
include "cfl.mm"
include "clt.mm"
include "cz.mm"
include "crp.mm"
include "nnred.mm"
include "prmgt1.mm"
include "jca.mm"
include "syl.mm"
include "nnz.mm"
include "3rp.mm"
include "efexple.mm"
include "syl3anc.mm"
include "oddprmge3.mm"
include "eluzle.mm"
include "nnrp.mm"
include "logled.mm"
include "mpbid.mm"
include "relogcl.mm"
include "rplogcl.mm"
include "divle1le.mm"
include "sylancr.mm"
include "mpbird.mm"
include "fldivle.mm"
include "relogcld.mm"
include "wne.mm"
include "cc0.mm"
include "nnrpd.mm"
include "1red.mm"
include "gtned.mm"
include "logne0.mm"
include "redivcld.mm"
include "flcld.mm"
include "zred.mm"
include "letr.mm"
include "nnge1.mm"
include "letri3d.mm"
include "syl5rbb.mm"
include "biimpd.mm"
include "mpand.mm"
include "syld.mm"
include "expd.mm"
include "mpan2d.mm"
include "mpid.mm"
include "sylbid.mm"
include "sq1.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "eqeq1i.mm"
include "caddc.mm"
include "eluzge2nn0.mm"
include "nn0expcld.mm"
include "1nn0.mm"
include "1p1e2.mm"
include "eluz2gt1.mm"
include "2re.mm"
include "1zzd.mm"
include "eluzelz.mm"
include "1lt2.mm"
include "ltexp2d.mm"
include "syl5eqbr.mm"
include "anim12i.mm"
include "3adant3.mm"
include "difsqpwdvds.mm"
include "syl31anc.mm"
include "2t1e2.mm"
include "breq2i.mm"
include "prmuz2.mm"
include "2prm.mm"
include "dvdsprm.mm"
include "sylancl.mm"
include "syl5bb.mm"
include "eldifsn.mm"
include "eqneqall.mm"
include "com12.mm"
include "simplbiim.mm"
include "jaoi.mm"
include "sylbi.mm"
include "impcom.mm"
include "rexlimdva.mm"
include "3imp.mm"

theorem lighneallem2
  let cP: class P
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( P e. ( Prime \ { 2 } ) /\ M e. NN /\ N e. NN ) /\ 2 || N /\ ( ( 2 ^ N ) - 1 ) = ( P ^ M ) ) -> M = 1 )

  proof
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    c2
    cN
    cdvds
    wbr
    #
    c2
    cN
    cexp
    co
    #
    c1
    cmin
    co
    #
    cP
    cM
    cexp
    co
    #
    wceq
    #
    cM
    c1
    wceq
    #
    @4
    @5
    c2
    vk
    cv
    #
    cmul
    co
    #
    cN
    wceq
    #
    vk
    cn
    wrex
    #
    @9
    @10
    wi
    #
    @3
    @1
    @5
    @14
    wb
    @2
    vk
    cN
    evennn2n
    3ad2ant3
    @4
    @13
    @15
    vk
    cn
    @4
    @11
    cn
    wcel
    #
    wa
    #
    @13
    @15
    @17
    @13
    wa
    #
    @9
    c2
    @11
    cexp
    co
    #
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    @8
    wceq
    #
    @10
    @18
    @7
    @21
    @8
    @18
    @6
    @20
    c1
    cmin
    @13
    @17
    @6
    c2
    @12
    cexp
    co
    #
    @20
    @6
    @23
    wceq
    cN
    @12
    cN
    @12
    c2
    cexp
    oveq2
    eqcoms
    @16
    @23
    @20
    wceq
    @4
    @16
    @23
    c2
    @11
    c2
    cmul
    co
    #
    cexp
    co
    @20
    @16
    @12
    @24
    c2
    cexp
    @16
    c2
    @11
    @16
    2cnd
    #
    @11
    nncn
    mulcomd
    oveq2d
    @16
    c2
    @11
    c2
    @25
    c2
    cn0
    wcel
    #
    @16
    2nn0
    a1i
    @11
    nnnn0
    expmuld
    eqtrd
    adantl
    sylan9eqr
    oveq1d
    eqeq1d
    @17
    @22
    @10
    wi
    #
    @13
    @16
    @4
    @27
    @16
    @11
    c1
    wceq
    #
    @11
    c2
    cuz
    cfv
    #
    wcel
    #
    wo
    @4
    @27
    wi
    #
    @11
    elnn1uz2
    @28
    @31
    @30
    @28
    @4
    @27
    @28
    @4
    wa
    @22
    c3
    @8
    wceq
    #
    @10
    @28
    @22
    @32
    wb
    @4
    @28
    @21
    c3
    @8
    @28
    @21
    c2
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c3
    @28
    @20
    @33
    c1
    cmin
    @28
    @19
    c2
    c2
    cexp
    @28
    @19
    c2
    c1
    cexp
    co
    #
    c2
    @11
    c1
    c2
    cexp
    oveq2
    c2
    cc
    wcel
    @35
    c2
    wceq
    2cn
    c2
    exp1
    ax-mp
    #
    syl6eq
    oveq1d
    oveq1d
    @34
    c4
    c1
    cmin
    co
    c3
    @33
    c4
    c1
    cmin
    sq2
    oveq1i
    4m1e3
    eqtri
    syl6eq
    eqeq1d
    adantr
    @4
    @32
    @10
    wi
    @28
    @4
    @32
    @8
    c3
    cle
    wbr
    #
    @10
    @32
    @8
    c3
    wceq
    #
    @4
    @37
    c3
    @8
    eqcom
    @4
    @38
    @37
    @4
    @38
    wa
    @8
    c3
    @4
    @8
    cr
    wcel
    @38
    @4
    cP
    cM
    @1
    @2
    cP
    cr
    wcel
    #
    @3
    @1
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    #
    @39
    cP
    cprime
    @0
    eldifi
    #
    cP
    prmnn
    #
    cP
    nnre
    3syl
    3ad2ant1
    @2
    @1
    cM
    cn0
    wcel
    #
    @3
    cM
    nnnn0
    #
    3ad2ant2
    reexpcld
    adantr
    @4
    @38
    simpr
    eqled
    ex
    syl5bi
    @4
    @37
    cM
    c3
    clog
    cfv
    #
    cP
    clog
    cfv
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cle
    wbr
    #
    @10
    @4
    @39
    c1
    cP
    clt
    wbr
    #
    wa
    #
    cM
    cz
    wcel
    #
    c3
    crp
    wcel
    #
    @37
    @50
    wb
    @1
    @2
    @52
    @3
    @1
    @40
    @52
    @42
    @40
    @39
    @51
    @40
    cP
    @43
    nnred
    cP
    prmgt1
    #
    jca
    #
    syl
    3ad2ant1
    @2
    @1
    @53
    @3
    cM
    nnz
    3ad2ant2
    @54
    @4
    3rp
    a1i
    cP
    c3
    cM
    efexple
    syl3anc
    @4
    @50
    @48
    c1
    cle
    wbr
    #
    @10
    @4
    @57
    @46
    @47
    cle
    wbr
    #
    @1
    @2
    @58
    @3
    @1
    c3
    cP
    cle
    wbr
    #
    @58
    @1
    cP
    c3
    cuz
    cfv
    wcel
    @59
    cP
    oddprmge3
    c3
    cP
    eluzle
    syl
    @1
    c3
    cP
    @54
    @1
    3rp
    a1i
    @1
    @40
    @41
    cP
    crp
    wcel
    #
    @42
    @43
    cP
    nnrp
    #
    3syl
    logled
    mpbid
    3ad2ant1
    @4
    @46
    cr
    wcel
    #
    @47
    crp
    wcel
    #
    @57
    @58
    wb
    @54
    @62
    3rp
    c3
    relogcl
    ax-mp
    #
    @1
    @2
    @63
    @3
    @1
    @40
    @52
    @63
    @42
    @56
    cP
    rplogcl
    3syl
    3ad2ant1
    #
    @46
    @47
    divle1le
    sylancr
    mpbird
    @4
    @50
    @49
    @48
    cle
    wbr
    #
    @57
    @10
    wi
    #
    @4
    @62
    @63
    @66
    @64
    @65
    @46
    @47
    fldivle
    sylancr
    @4
    @50
    @66
    wa
    #
    cM
    @48
    cle
    wbr
    #
    @67
    @4
    cM
    cr
    wcel
    #
    @49
    cr
    wcel
    #
    @48
    cr
    wcel
    #
    @68
    @69
    wi
    @2
    @1
    @70
    @3
    cM
    nnre
    #
    3ad2ant2
    #
    @1
    @2
    @71
    @3
    @1
    @49
    @1
    @48
    @1
    @46
    @47
    @62
    @1
    @64
    a1i
    @1
    @40
    @41
    @47
    cr
    wcel
    @42
    @43
    @41
    cP
    @61
    relogcld
    3syl
    @1
    @40
    @60
    cP
    c1
    wne
    #
    wa
    @47
    cc0
    wne
    @42
    @40
    @60
    @75
    @40
    cP
    @43
    nnrpd
    @40
    c1
    cP
    @40
    1red
    @55
    gtned
    jca
    cP
    logne0
    3syl
    redivcld
    #
    flcld
    zred
    3ad2ant1
    @1
    @2
    @72
    @3
    @76
    3ad2ant1
    #
    cM
    @49
    @48
    letr
    syl3anc
    @4
    @69
    @57
    @10
    @4
    @69
    @57
    wa
    #
    cM
    c1
    cle
    wbr
    #
    @10
    @4
    @70
    @72
    c1
    cr
    wcel
    @78
    @79
    wi
    @74
    @77
    @4
    1red
    cM
    @48
    c1
    letr
    syl3anc
    @2
    @1
    @79
    @10
    wi
    @3
    @2
    c1
    cM
    cle
    wbr
    #
    @79
    @10
    cM
    nnge1
    @2
    @80
    @79
    wa
    #
    @10
    @10
    c1
    cM
    wceq
    @2
    @81
    cM
    c1
    eqcom
    @2
    c1
    cM
    @2
    1red
    @73
    letri3d
    syl5rbb
    biimpd
    mpand
    3ad2ant2
    syld
    expd
    syld
    mpan2d
    mpid
    sylbid
    syld
    adantl
    sylbid
    ex
    @30
    @4
    @27
    @22
    @20
    c1
    c2
    cexp
    co
    #
    cmin
    co
    #
    @8
    wceq
    #
    @30
    @4
    wa
    #
    @10
    @21
    @83
    @8
    c1
    @82
    @20
    cmin
    @82
    c1
    sq1
    eqcomi
    oveq2i
    eqeq1i
    @84
    @8
    @83
    wceq
    #
    @85
    @10
    @83
    @8
    eqcom
    @85
    @86
    cP
    c2
    c1
    cmul
    co
    #
    cdvds
    wbr
    #
    @10
    @85
    @19
    cn0
    wcel
    #
    c1
    cn0
    wcel
    #
    c1
    c1
    caddc
    co
    #
    @19
    clt
    wbr
    #
    @40
    @44
    wa
    #
    @86
    @88
    wi
    @30
    @89
    @4
    @30
    c2
    @11
    @26
    @30
    2nn0
    a1i
    @11
    eluzge2nn0
    nn0expcld
    adantr
    @90
    @85
    1nn0
    a1i
    @30
    @92
    @4
    @30
    @91
    @35
    @19
    clt
    @91
    c2
    @35
    1p1e2
    @35
    c2
    @36
    eqcomi
    eqtri
    @30
    c1
    @11
    clt
    wbr
    @35
    @19
    clt
    wbr
    @11
    eluz2gt1
    @30
    c2
    c1
    @11
    c2
    cr
    wcel
    @30
    2re
    a1i
    @30
    1zzd
    c2
    @11
    eluzelz
    c1
    c2
    clt
    wbr
    @30
    1lt2
    a1i
    ltexp2d
    mpbid
    syl5eqbr
    adantr
    @4
    @93
    @30
    @1
    @2
    @93
    @3
    @1
    @40
    @2
    @44
    @42
    @45
    anim12i
    3adant3
    adantl
    @19
    c1
    cP
    cM
    difsqpwdvds
    syl31anc
    @4
    @88
    @10
    wi
    #
    @30
    @1
    @2
    @94
    @3
    @1
    @88
    cP
    c2
    wceq
    #
    @10
    @88
    cP
    c2
    cdvds
    wbr
    #
    @1
    @95
    @87
    c2
    cP
    cdvds
    2t1e2
    breq2i
    @1
    cP
    @29
    wcel
    #
    c2
    cprime
    wcel
    @96
    @95
    wb
    @1
    @40
    @97
    @42
    cP
    prmuz2
    syl
    2prm
    c2
    cP
    dvdsprm
    sylancl
    syl5bb
    @1
    @40
    cP
    c2
    wne
    #
    @95
    @10
    wi
    cP
    cprime
    c2
    eldifsn
    @95
    @98
    @10
    @10
    cP
    c2
    eqneqall
    com12
    simplbiim
    sylbid
    3ad2ant1
    adantl
    syld
    syl5bi
    syl5bi
    ex
    jaoi
    sylbi
    impcom
    adantr
    sylbid
    ex
    rexlimdva
    sylbid
    3imp
end
