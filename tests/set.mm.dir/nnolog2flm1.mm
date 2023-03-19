include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cn.mm"
include "clogb.mm"
include "cfl.mm"
include "cmin.mm"
include "wceq.mm"
include "cblen.mm"
include "cexp.mm"
include "cfzo.mm"
include "wo.mm"
include "wi.mm"
include "eluz2nn.mm"
include "nnpw2blenfzo2.mm"
include "syl.mm"
include "wa.mm"
include "wn.mm"
include "wb.mm"
include "adantl.mm"
include "nneo.mm"
include "bicomd.mm"
include "notnotb.mm"
include "syl6bb.mm"
include "con4bid.mm"
include "simpl.mm"
include "oveq1d.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "blennnelnn.mm"
include "nnnn0d.mm"
include "2m1e1.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "1ne2.mm"
include "necomi.mm"
include "logbid1.mm"
include "mp3an.mm"
include "eluzle.mm"
include "crp.mm"
include "cz.mm"
include "2z.mm"
include "uzid.mm"
include "mp1i.mm"
include "2rp.mm"
include "a1i.mm"
include "nnrpd.mm"
include "logbleb.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "cr.mm"
include "relogbcl.mm"
include "1zzd.mm"
include "flge.mm"
include "syl2anc.mm"
include "syl5eqbr.mm"
include "2re.mm"
include "1red.mm"
include "flcld.mm"
include "zred.mm"
include "lesubaddd.mm"
include "blennn.mm"
include "breqtrrd.mm"
include "nn0ge2m1nn.mm"
include "nnpw2even.mm"
include "eqeltrd.mm"
include "pm2.24d.mm"
include "sylbid.mm"
include "ex.mm"
include "nnm1nn0.mm"
include "ad2antlr.mm"
include "nnpw2blenfzo.mm"
include "nncnd.mm"
include "npcan1.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "fllog2.mm"
include "clt.mm"
include "w3a.mm"
include "elfzo2.mm"
include "eluz2.mm"
include "3anbi1i.mm"
include "bitri.mm"
include "2nn.mm"
include "jca.mm"
include "nnexpcl.mm"
include "nnzd.mm"
include "peano2zm.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "nnexpcld.mm"
include "nnred.mm"
include "leaddsub.mm"
include "biimpcd.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "syl3anbrc.mm"
include "eleq1d.mm"
include "mpbird.mm"
include "ltle.mm"
include "nnre.mm"
include "reexpcld.mm"
include "syl11.mm"
include "simpll2.mm"
include "zlem1lt.mm"
include "3jca.mm"
include "3adant2.mm"
include "sylbi.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "exp31.mm"
include "jaoi.mm"
include "mpcom.mm"

theorem nnolog2flm1
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. ( ZZ>= ` 2 ) /\ ( ( N + 1 ) / 2 ) e. NN ) -> ( |_ ` ( 2 logb N ) ) = ( |_ ` ( 2 logb ( N - 1 ) ) ) )

  proof
    cN
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    cn
    wcel
    #
    c2
    cN
    clogb
    co
    #
    cfl
    cfv
    #
    c2
    cN
    c1
    cmin
    co
    #
    clogb
    co
    cfl
    cfv
    #
    wceq
    #
    cN
    c2
    cN
    cblen
    cfv
    #
    c1
    cmin
    co
    #
    cexp
    co
    #
    wceq
    #
    cN
    @10
    c1
    caddc
    co
    #
    c2
    @8
    cexp
    co
    #
    cfzo
    co
    wcel
    #
    wo
    #
    @1
    @2
    @7
    wi
    #
    @1
    cN
    cn
    wcel
    #
    @15
    cN
    eluz2nn
    #
    cN
    nnpw2blenfzo2
    syl
    @11
    @1
    @16
    wi
    @14
    @11
    @1
    @16
    @11
    @1
    wa
    #
    @2
    cN
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    wn
    #
    @7
    @19
    @2
    @22
    @19
    @2
    wn
    #
    @21
    @22
    wn
    @19
    @17
    @23
    @21
    wb
    @1
    @17
    @11
    @18
    adantl
    @17
    @21
    @23
    cN
    nneo
    bicomd
    syl
    @21
    notnotb
    syl6bb
    con4bid
    @19
    @21
    @7
    @19
    @20
    @10
    c2
    cdiv
    co
    #
    cn
    @19
    cN
    @10
    c2
    cdiv
    @11
    @1
    simpl
    oveq1d
    @19
    @9
    cn
    wcel
    #
    @24
    cn
    wcel
    @1
    @25
    @11
    @1
    @8
    cn0
    wcel
    #
    c2
    @8
    cle
    wbr
    @25
    @1
    @17
    @26
    @18
    @17
    @8
    cN
    blennnelnn
    #
    nnnn0d
    #
    syl
    #
    @1
    c2
    @4
    c1
    caddc
    co
    #
    @8
    cle
    @1
    c2
    c1
    cmin
    co
    #
    @4
    cle
    wbr
    c2
    @30
    cle
    wbr
    @1
    @31
    c1
    @4
    cle
    2m1e1
    @1
    c1
    @3
    cle
    wbr
    #
    c1
    @4
    cle
    wbr
    #
    @1
    c1
    c2
    c2
    clogb
    co
    #
    @3
    cle
    c2
    cc
    wcel
    c2
    cc0
    wne
    c2
    c1
    wne
    #
    @34
    c1
    wceq
    2cn
    2ne0
    c1
    c2
    1ne2
    necomi
    #
    c2
    logbid1
    mp3an
    @1
    c2
    cN
    cle
    wbr
    #
    @34
    @3
    cle
    wbr
    #
    c2
    cN
    eluzle
    @1
    c2
    @0
    wcel
    #
    c2
    crp
    wcel
    #
    cN
    crp
    wcel
    #
    @37
    @38
    wb
    c2
    cz
    wcel
    @39
    @1
    2z
    c2
    uzid
    mp1i
    @40
    @1
    2rp
    a1i
    #
    @1
    cN
    @18
    nnrpd
    #
    c2
    c2
    cN
    logbleb
    syl3anc
    mpbid
    syl5eqbrr
    @1
    @3
    cr
    wcel
    #
    c1
    cz
    wcel
    @32
    @33
    wb
    @1
    @40
    @41
    @35
    @44
    @42
    @43
    @35
    @1
    @36
    a1i
    c2
    cN
    relogbcl
    syl3anc
    #
    @1
    1zzd
    @3
    c1
    flge
    syl2anc
    mpbid
    syl5eqbr
    @1
    c2
    c1
    @4
    c2
    cr
    wcel
    #
    @1
    2re
    a1i
    @1
    1red
    #
    @1
    @4
    @1
    @3
    @45
    flcld
    zred
    lesubaddd
    mpbid
    @1
    @17
    @8
    @30
    wceq
    @18
    cN
    blennn
    syl
    breqtrrd
    @8
    nn0ge2m1nn
    syl2anc
    adantl
    @9
    nnpw2even
    syl
    eqeltrd
    pm2.24d
    sylbid
    ex
    @14
    @1
    @2
    @7
    @14
    @1
    wa
    #
    @2
    wa
    #
    @4
    @9
    @6
    @49
    @9
    cn0
    wcel
    #
    cN
    @10
    c2
    @9
    c1
    caddc
    co
    #
    cexp
    co
    #
    cfzo
    co
    #
    wcel
    @4
    @9
    wceq
    @1
    @50
    @14
    @2
    @1
    @8
    cn
    wcel
    #
    @50
    @1
    @17
    @54
    @18
    @27
    syl
    #
    @8
    nnm1nn0
    #
    syl
    #
    ad2antlr
    @49
    cN
    @10
    @13
    cfzo
    co
    #
    @53
    @49
    @17
    cN
    @58
    wcel
    @1
    @17
    @14
    @2
    @18
    ad2antlr
    cN
    nnpw2blenfzo
    syl
    @49
    @52
    @13
    @10
    cfzo
    @49
    @51
    @8
    c2
    cexp
    @49
    @8
    cc
    wcel
    #
    @51
    @8
    wceq
    #
    @1
    @59
    @14
    @2
    @1
    @8
    @55
    nncnd
    #
    ad2antlr
    @8
    npcan1
    #
    syl
    oveq2d
    oveq2d
    eleqtrrd
    @9
    cN
    fllog2
    syl2anc
    @49
    @50
    @5
    @53
    wcel
    #
    @6
    @9
    wceq
    @49
    @54
    @50
    @1
    @54
    @14
    @2
    @55
    ad2antlr
    @56
    syl
    @48
    @63
    @2
    @48
    @5
    @10
    cuz
    cfv
    wcel
    #
    @52
    cz
    wcel
    #
    @5
    @52
    clt
    wbr
    #
    w3a
    #
    @63
    @14
    @1
    @67
    @14
    @12
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @12
    cN
    cle
    wbr
    #
    w3a
    #
    @13
    cz
    wcel
    #
    cN
    @13
    clt
    wbr
    #
    w3a
    #
    @1
    @67
    wi
    #
    @14
    cN
    @12
    cuz
    cfv
    wcel
    #
    @72
    @73
    w3a
    @74
    cN
    @12
    @13
    elfzo2
    @76
    @71
    @72
    @73
    @12
    cN
    eluz2
    3anbi1i
    bitri
    @71
    @73
    @75
    @72
    @71
    @73
    wa
    #
    @1
    @67
    @77
    @1
    wa
    #
    @64
    @65
    @66
    @78
    @10
    cz
    wcel
    @5
    cz
    wcel
    #
    @10
    @5
    cle
    wbr
    #
    @64
    @78
    @10
    @78
    c2
    cn
    wcel
    #
    @50
    wa
    #
    @10
    cn
    wcel
    @1
    @82
    @77
    @1
    @81
    @50
    @81
    @1
    2nn
    a1i
    #
    @57
    jca
    adantl
    c2
    @9
    nnexpcl
    syl
    nnzd
    @77
    @79
    @1
    @71
    @79
    @73
    @69
    @68
    @79
    @70
    cN
    peano2zm
    3ad2ant2
    adantr
    adantr
    @77
    @1
    @80
    @71
    @1
    @80
    wi
    #
    @73
    @70
    @68
    @84
    @69
    @1
    @70
    @80
    @1
    @10
    cr
    wcel
    c1
    cr
    wcel
    cN
    cr
    wcel
    #
    @70
    @80
    wb
    @1
    @10
    @1
    c2
    @9
    @83
    @57
    nnexpcld
    nnred
    @47
    @1
    cN
    @18
    nnred
    @10
    c1
    cN
    leaddsub
    syl3anc
    biimpcd
    3ad2ant3
    adantr
    imp
    @10
    @5
    eluz2
    syl3anbrc
    @78
    @52
    @78
    @81
    @51
    cn0
    wcel
    #
    wa
    #
    @52
    cn
    wcel
    @1
    @87
    @77
    @1
    @81
    @86
    @83
    @1
    @86
    @26
    @29
    @1
    @59
    @86
    @26
    wb
    @61
    @59
    @51
    @8
    cn0
    @62
    eleq1d
    syl
    mpbird
    jca
    adantl
    c2
    @51
    nnexpcl
    syl
    nnzd
    @78
    @5
    @13
    @52
    clt
    @78
    cN
    @13
    cle
    wbr
    #
    @5
    @13
    clt
    wbr
    #
    @77
    @1
    @88
    @73
    @1
    @88
    wi
    @71
    @85
    @13
    cr
    wcel
    #
    wa
    #
    @73
    @88
    @1
    cN
    @13
    ltle
    @1
    @17
    @91
    @18
    @17
    @85
    @90
    cN
    nnre
    @17
    c2
    @8
    @46
    @17
    2re
    a1i
    @28
    reexpcld
    jca
    syl
    syl11
    adantl
    imp
    @78
    @69
    @72
    @88
    @89
    wb
    @68
    @69
    @70
    @73
    @1
    simpll2
    @1
    @72
    @77
    @1
    @13
    @1
    c2
    @8
    @83
    @29
    nnexpcld
    nnzd
    adantl
    cN
    @13
    zlem1lt
    syl2anc
    mpbid
    @1
    @52
    @13
    wceq
    @77
    @1
    @51
    @8
    c2
    cexp
    @1
    @59
    @60
    @61
    @62
    syl
    oveq2d
    adantl
    breqtrrd
    3jca
    ex
    3adant2
    sylbi
    imp
    @5
    @10
    @52
    elfzo2
    sylibr
    adantr
    @9
    @5
    fllog2
    syl2anc
    eqtr4d
    exp31
    jaoi
    mpcom
    imp
end
