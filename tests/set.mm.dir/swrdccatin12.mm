include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "cconcat.mm"
include "cop.mm"
include "csubstr.mm"
include "cmin.mm"
include "wceq.mm"
include "cfzo.mm"
include "wfn.mm"
include "ccatcl.mm"
include "adantr.mm"
include "elfz0fzfz0.mm"
include "adantl.mm"
include "cuz.mm"
include "wss.mm"
include "elfzuz2.mm"
include "fzss1.mm"
include "syl.mm"
include "ccatlen.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "sseqtr4d.mm"
include "sseld.mm"
include "impr.mm"
include "swrdvalfn.mm"
include "syl3anc.mm"
include "swrdcl.mm"
include "anim12i.mm"
include "ccatvalfn.mm"
include "simpll.mm"
include "simprl.mm"
include "cn0.mm"
include "lencl.mm"
include "elnn0uz.mm"
include "eluzfz2.mm"
include "sylbi.mm"
include "syl5eqel.mm"
include "swrdlen.mm"
include "simpr.mm"
include "cz.mm"
include "nn0zd.mm"
include "elfzmlbp.mm"
include "swrd0len.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "cc.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "elfz2nn0.mm"
include "nn0cn.mm"
include "ad2antrl.mm"
include "zcn.mm"
include "3jca.mm"
include "ex.mm"
include "elfzelz.mm"
include "syl11.mm"
include "3adant3.mm"
include "imp.mm"
include "npncan3.mm"
include "eqtr2d.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "cv.mm"
include "anim2i.mm"
include "ancomd.mm"
include "swrdccatin12lem3.mm"
include "sylc.mm"
include "simpl.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "eleqtrrd.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "ccatval1.mm"
include "eqtr4d.mm"
include "wn.mm"
include "swrdccatin12lem2.mm"
include "elfzuz.mm"
include "eluzelz.mm"
include "ancoms.mm"
include "syl5com.mm"
include "impcom.mm"
include "swrdccatin12lem1.mm"
include "jca.mm"
include "ccatval2.mm"
include "pm2.61ian.mm"
include "eqfnfvd.mm"

theorem swrdccatin12
  let cA: class A
  let cB: class B
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume swrdccatin12.l: |- L = ( # ` A )


  assert |- ( ( A e. Word V /\ B e. Word V ) -> ( ( M e. ( 0 ... L ) /\ N e. ( L ... ( L + ( # ` B ) ) ) ) -> ( ( A ++ B ) substr <. M , N >. ) = ( ( A substr <. M , L >. ) ++ ( B substr <. 0 , ( N - L ) >. ) ) ) )

  proof
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cM
    cc0
    cL
    cfz
    co
    wcel
    #
    cN
    cL
    cL
    cB
    chash
    cfv
    #
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cA
    cB
    cconcat
    co
    #
    cM
    cN
    cop
    csubstr
    co
    #
    cA
    cM
    cL
    cop
    csubstr
    co
    #
    cB
    cc0
    cN
    cL
    cmin
    co
    #
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    wceq
    @3
    @9
    wa
    #
    vk
    cc0
    cN
    cM
    cmin
    co
    #
    cfzo
    co
    #
    @11
    @15
    @16
    @10
    @0
    wcel
    #
    cM
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cc0
    @10
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @11
    @18
    wfn
    @3
    @19
    @9
    cV
    cA
    cB
    ccatcl
    adantr
    @9
    @20
    @3
    cL
    cM
    cN
    @6
    elfz0fzfz0
    adantl
    @3
    @4
    @8
    @23
    @3
    @4
    wa
    #
    @7
    @22
    cN
    @24
    @7
    cc0
    @6
    cfz
    co
    #
    @22
    @24
    cL
    cc0
    cuz
    cfv
    #
    wcel
    #
    @7
    @25
    wss
    @4
    @27
    @3
    cM
    cc0
    cL
    elfzuz2
    adantl
    cL
    cc0
    @6
    fzss1
    syl
    @24
    @21
    @6
    cc0
    cfz
    @3
    @21
    @6
    wceq
    @4
    @3
    @21
    cA
    chash
    cfv
    #
    @5
    caddc
    co
    @6
    cV
    cA
    cB
    ccatlen
    @28
    cL
    @5
    caddc
    cL
    @28
    swrdccatin12.l
    eqcomi
    oveq1i
    syl6eq
    adantr
    oveq2d
    sseqtr4d
    sseld
    impr
    @10
    cM
    cN
    cV
    swrdvalfn
    syl3anc
    @16
    @15
    @18
    wfn
    @15
    cc0
    @12
    chash
    cfv
    #
    @14
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    wfn
    #
    @16
    @12
    @0
    wcel
    #
    @14
    @0
    wcel
    #
    wa
    #
    @33
    @3
    @36
    @9
    @1
    @34
    @2
    @35
    cV
    cA
    cM
    cL
    swrdcl
    cV
    cB
    cc0
    @13
    swrdcl
    anim12i
    adantr
    #
    @12
    @14
    cV
    ccatvalfn
    syl
    @16
    @18
    @32
    @15
    @16
    @17
    @31
    cc0
    cfzo
    @16
    @31
    cL
    cM
    cmin
    co
    #
    @13
    caddc
    co
    #
    @17
    @16
    @29
    @38
    @30
    @13
    caddc
    @16
    @1
    @4
    cL
    cc0
    @28
    cfz
    co
    #
    wcel
    #
    @29
    @38
    wceq
    #
    @1
    @2
    @9
    simpll
    #
    @3
    @4
    @8
    simprl
    #
    @3
    @41
    @9
    @1
    @41
    @2
    @1
    @28
    cn0
    wcel
    #
    @41
    cV
    cA
    lencl
    #
    @45
    cL
    @28
    @40
    swrdccatin12.l
    @45
    @28
    @26
    wcel
    @28
    @40
    wcel
    #
    @28
    elnn0uz
    cc0
    @28
    eluzfz2
    sylbi
    syl5eqel
    syl
    adantr
    adantr
    cV
    cA
    cM
    cL
    swrdlen
    #
    syl3anc
    @16
    @2
    @13
    cc0
    @5
    cfz
    co
    wcel
    #
    @30
    @13
    wceq
    #
    @3
    @2
    @9
    @1
    @2
    simpr
    #
    adantr
    @16
    @5
    cz
    wcel
    #
    @8
    wa
    @49
    @3
    @52
    @9
    @8
    @2
    @52
    @1
    @2
    @5
    cV
    cB
    lencl
    nn0zd
    adantl
    #
    @4
    @8
    simpr
    anim12i
    cN
    cL
    @5
    elfzmlbp
    #
    syl
    cV
    cB
    @13
    swrd0len
    #
    syl2anc
    oveq12d
    @16
    cL
    cc
    wcel
    #
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    w3a
    #
    @39
    @17
    wceq
    @9
    @59
    @3
    @4
    @8
    @59
    @4
    cM
    cn0
    wcel
    #
    cL
    cn0
    wcel
    #
    cM
    cL
    cle
    wbr
    #
    w3a
    #
    @8
    @59
    wi
    #
    cM
    cL
    elfz2nn0
    #
    @60
    @61
    @64
    @62
    cN
    cz
    wcel
    #
    @60
    @61
    wa
    #
    @59
    @8
    @66
    @67
    @59
    @66
    @67
    wa
    @56
    @57
    @58
    @67
    @56
    @66
    @61
    @56
    @60
    cL
    nn0cn
    adantl
    adantl
    @60
    @57
    @66
    @61
    cM
    nn0cn
    ad2antrl
    @66
    @58
    @67
    cN
    zcn
    adantr
    3jca
    ex
    cN
    cL
    @6
    elfzelz
    syl11
    3adant3
    sylbi
    imp
    adantl
    cL
    cM
    cN
    npncan3
    syl
    eqtr2d
    oveq2d
    fneq2d
    mpbird
    vk
    cv
    #
    cc0
    @38
    cfzo
    co
    #
    wcel
    #
    @16
    @68
    @18
    wcel
    #
    wa
    #
    @68
    @11
    cfv
    #
    @68
    @15
    cfv
    #
    wceq
    @70
    @72
    wa
    #
    @73
    @68
    @12
    cfv
    #
    @74
    @75
    @16
    @71
    @70
    wa
    @73
    @76
    wceq
    @70
    @16
    @71
    simprl
    @75
    @70
    @71
    @72
    @71
    @70
    @16
    @71
    simpr
    #
    anim2i
    ancomd
    cA
    cB
    @68
    cL
    cM
    cN
    cV
    swrdccatin12.l
    swrdccatin12lem3
    sylc
    @75
    @34
    @35
    @68
    cc0
    @29
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    @74
    @76
    wceq
    @75
    @36
    @79
    @80
    @16
    @36
    @70
    @71
    @37
    ad2antrl
    @75
    @68
    @69
    @78
    @70
    @72
    simpl
    @75
    @29
    @38
    cc0
    cfzo
    @75
    @1
    @4
    @41
    w3a
    #
    @42
    @16
    @81
    @70
    @71
    @16
    @1
    @4
    @41
    @43
    @44
    @3
    @41
    @9
    @1
    @41
    @2
    @1
    cL
    @28
    @40
    swrdccatin12.l
    @1
    @45
    @47
    @46
    @28
    nn0fz0
    sylib
    syl5eqel
    adantr
    adantr
    #
    3jca
    ad2antrl
    @48
    syl
    oveq2d
    eleqtrrd
    @34
    @35
    @79
    df-3an
    sylanbrc
    cV
    @12
    @14
    @68
    ccatval1
    syl
    eqtr4d
    @70
    wn
    #
    @72
    wa
    #
    @73
    @68
    @29
    cmin
    co
    @14
    cfv
    #
    @74
    @84
    @16
    @71
    @83
    wa
    #
    @73
    @85
    wceq
    @83
    @16
    @71
    simprl
    @84
    @83
    @71
    @72
    @71
    @83
    @77
    anim2i
    ancomd
    #
    cA
    cB
    @68
    cL
    cM
    cN
    cV
    swrdccatin12.l
    swrdccatin12lem2
    sylc
    @84
    @34
    @35
    @68
    @29
    @31
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    @74
    @85
    wceq
    @84
    @36
    @89
    @90
    @16
    @36
    @83
    @71
    @37
    ad2antrl
    @84
    @68
    @38
    @39
    cfzo
    co
    #
    @88
    @84
    @61
    @60
    @66
    w3a
    #
    @86
    @68
    @91
    wcel
    @16
    @92
    @83
    @71
    @9
    @92
    @3
    @8
    @4
    @92
    @8
    cN
    cL
    cuz
    cfv
    wcel
    #
    @4
    @92
    wi
    cN
    cL
    @6
    elfzuz
    @93
    @66
    @4
    @92
    cL
    cN
    eluzelz
    @4
    @63
    @66
    @92
    wi
    #
    @65
    @60
    @61
    @94
    @62
    @61
    @60
    @94
    @61
    @60
    wa
    #
    @66
    @92
    @95
    @66
    wa
    @61
    @60
    @66
    @61
    @60
    @66
    simpll
    @95
    @60
    @66
    @61
    @60
    simpr
    adantr
    @95
    @66
    simpr
    3jca
    ex
    ancoms
    3adant3
    sylbi
    syl5com
    syl
    impcom
    adantl
    ad2antrl
    @87
    @68
    cL
    cM
    cN
    swrdccatin12lem1
    sylc
    @16
    @88
    @91
    wceq
    @83
    @71
    @16
    @29
    @38
    @31
    @39
    cfzo
    @16
    @1
    @4
    @41
    @42
    @43
    @44
    @82
    @48
    syl3anc
    #
    @16
    @29
    @38
    @30
    @13
    caddc
    @96
    @16
    @2
    @49
    wa
    #
    @50
    @9
    @3
    @97
    @8
    @3
    @97
    wi
    @4
    @8
    @3
    @97
    @8
    @3
    wa
    #
    @2
    @49
    @3
    @2
    @8
    @51
    adantl
    @98
    @52
    @8
    @49
    @3
    @52
    @8
    @53
    adantl
    @8
    @3
    simpl
    @54
    syl2anc
    jca
    ex
    adantl
    impcom
    @55
    syl
    oveq12d
    oveq12d
    ad2antrl
    eleqtrrd
    @34
    @35
    @89
    df-3an
    sylanbrc
    cV
    @12
    @14
    @68
    ccatval2
    syl
    eqtr4d
    pm2.61ian
    eqfnfvd
    ex
end
