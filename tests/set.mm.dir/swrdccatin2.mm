include "cword.mm"
include "wcel.mm"
include "wa.mm"
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
include "cc0.mm"
include "cfzo.mm"
include "wfn.mm"
include "wb.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "anbi12d.mm"
include "ax-mp.mm"
include "wi.mm"
include "cn0.mm"
include "lencl.mm"
include "cuz.mm"
include "wss.mm"
include "elnn0uz.mm"
include "biimpi.mm"
include "fzss1.mm"
include "syl.mm"
include "sseld.mm"
include "anim12d.mm"
include "adantr.mm"
include "syl5bi.mm"
include "imp.mm"
include "swrdccatfn.mm"
include "syldan.mm"
include "cc.mm"
include "w3a.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "elfz2.mm"
include "zcn.mm"
include "3anim123i.mm"
include "3comr.mm"
include "sylbi.mm"
include "nnncan2.mm"
include "adantl.mm"
include "oveq2d.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "simpr.mm"
include "elfzmlbm.mm"
include "ad2antrl.mm"
include "elfzmlbp.mm"
include "ex.mm"
include "nn0zd.mm"
include "syl11.mm"
include "impcom.mm"
include "swrdvalfn.mm"
include "syl3anc.mm"
include "cv.mm"
include "clt.mm"
include "cif.mm"
include "simpl.mm"
include "elfzoelz.mm"
include "elfzelz.mm"
include "zaddcl.mm"
include "expcom.mm"
include "syl5com.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "ccatsymb.mm"
include "wn.mm"
include "elfzonn0.mm"
include "cr.mm"
include "zre.mm"
include "anim12i.mm"
include "elnn0z.mm"
include "0red.mm"
include "anim1i.mm"
include "ancoms.mm"
include "anim2i.mm"
include "le2add.mm"
include "syl2anc.mm"
include "recn.mm"
include "addid2d.mm"
include "breq1d.mm"
include "sylibd.mm"
include "readdcl.mm"
include "lenltd.mm"
include "expd.mm"
include "com12.mm"
include "mpan9.mm"
include "eqcomi.mm"
include "breq2i.mm"
include "notbii.mm"
include "syl6ibr.mm"
include "com23.mm"
include "3adant2.mm"
include "iffalsed.mm"
include "ad2antrr.mm"
include "addsubassd.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "syl5ib.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "ccatcl.mm"
include "syl5eqel.mm"
include "3syl.mm"
include "ccatlen.mm"
include "fzmmmeqm.mm"
include "biimpd.mm"
include "swrdfv.mm"
include "syl31anc.mm"
include "3jca.mm"
include "sylan.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"

theorem swrdccatin2
  let cA: class A
  let cB: class B
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume swrdccatin12.l: |- L = ( # ` A )


  assert |- ( ( A e. Word V /\ B e. Word V ) -> ( ( M e. ( L ... N ) /\ N e. ( L ... ( L + ( # ` B ) ) ) ) -> ( ( A ++ B ) substr <. M , N >. ) = ( B substr <. ( M - L ) , ( N - L ) >. ) ) )

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
    cL
    cN
    cfz
    co
    #
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
    cB
    cM
    cL
    cmin
    co
    #
    cN
    cL
    cmin
    co
    #
    cop
    csubstr
    co
    #
    wceq
    @3
    @10
    wa
    #
    vk
    cc0
    @14
    @13
    cmin
    co
    #
    cfzo
    co
    #
    @12
    @15
    @16
    @12
    @18
    wfn
    @12
    cc0
    cN
    cM
    cmin
    co
    #
    cfzo
    co
    #
    wfn
    #
    @3
    @10
    cM
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cN
    cc0
    cA
    chash
    cfv
    #
    @6
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
    @21
    @3
    @10
    @28
    @10
    cM
    @24
    cN
    cfz
    co
    #
    wcel
    #
    cN
    @24
    @25
    cfz
    co
    #
    wcel
    #
    wa
    #
    @3
    @28
    cL
    @24
    wceq
    #
    @10
    @33
    wb
    swrdccatin12.l
    @34
    @5
    @30
    @9
    @32
    @34
    @4
    @29
    cM
    cL
    @24
    cN
    cfz
    oveq1
    eleq2d
    @34
    @8
    @31
    cN
    @34
    cL
    @24
    @7
    @25
    cfz
    @34
    id
    cL
    @24
    @6
    caddc
    oveq1
    oveq12d
    eleq2d
    #
    anbi12d
    ax-mp
    @1
    @33
    @28
    wi
    #
    @2
    @1
    @24
    cn0
    wcel
    #
    @36
    cV
    cA
    lencl
    #
    @37
    @30
    @23
    @32
    @27
    @37
    @29
    @22
    cM
    @37
    @24
    cc0
    cuz
    cfv
    #
    wcel
    #
    @29
    @22
    wss
    @37
    @40
    @24
    elnn0uz
    biimpi
    #
    @24
    cc0
    cN
    fzss1
    syl
    sseld
    @37
    @31
    @26
    cN
    @37
    @40
    @31
    @26
    wss
    #
    @41
    @24
    cc0
    @25
    fzss1
    #
    syl
    sseld
    anim12d
    syl
    adantr
    syl5bi
    imp
    cA
    cB
    cM
    cN
    cV
    swrdccatfn
    syldan
    @16
    @18
    @20
    @12
    @16
    @17
    @19
    cc0
    cfzo
    @10
    @17
    @19
    wceq
    #
    @3
    @10
    cN
    cc
    wcel
    #
    cM
    cc
    wcel
    #
    cL
    cc
    wcel
    #
    w3a
    #
    @44
    @5
    @48
    @9
    @5
    cL
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    w3a
    #
    cL
    cM
    cle
    wbr
    #
    cM
    cN
    cle
    wbr
    #
    wa
    #
    wa
    #
    @48
    cM
    cL
    cN
    elfz2
    #
    @52
    @48
    @55
    @50
    @51
    @49
    @48
    @50
    @45
    @51
    @46
    @49
    @47
    cN
    zcn
    cM
    zcn
    #
    cL
    zcn
    #
    3anim123i
    3comr
    adantr
    sylbi
    adantr
    cN
    cM
    cL
    nnncan2
    syl
    adantl
    oveq2d
    fneq2d
    mpbird
    @16
    @2
    @13
    cc0
    @14
    cfz
    co
    wcel
    #
    @14
    cc0
    @6
    cfz
    co
    wcel
    #
    @15
    @18
    wfn
    @3
    @2
    @10
    @1
    @2
    simpr
    adantr
    #
    @5
    @60
    @3
    @9
    cM
    cL
    cN
    elfzmlbm
    ad2antrl
    #
    @10
    @3
    @61
    @9
    @3
    @61
    wi
    #
    @5
    @6
    cz
    wcel
    #
    @9
    @61
    @3
    @65
    @9
    @61
    cN
    cL
    @6
    elfzmlbp
    ex
    #
    @2
    @65
    @1
    @2
    @6
    cV
    cB
    lencl
    nn0zd
    #
    adantl
    syl11
    adantl
    impcom
    cB
    @13
    @14
    cV
    swrdvalfn
    syl3anc
    @16
    vk
    cv
    #
    @18
    wcel
    #
    wa
    #
    @68
    cM
    caddc
    co
    #
    @11
    cfv
    #
    @68
    @13
    caddc
    co
    #
    cB
    cfv
    #
    @68
    @12
    cfv
    #
    @68
    @15
    cfv
    #
    @70
    @72
    @71
    @24
    clt
    wbr
    #
    @71
    cA
    cfv
    #
    @71
    @24
    cmin
    co
    #
    cB
    cfv
    #
    cif
    #
    @80
    @74
    @70
    @1
    @2
    @71
    cz
    wcel
    #
    w3a
    #
    @72
    @81
    wceq
    @70
    @3
    @82
    @83
    @16
    @3
    @69
    @3
    @10
    simpl
    adantr
    @69
    @16
    @82
    @69
    @68
    cz
    wcel
    #
    @16
    @82
    @68
    cc0
    @17
    elfzoelz
    #
    @5
    @84
    @82
    wi
    #
    @3
    @9
    @5
    @51
    @86
    cM
    cL
    cN
    elfzelz
    @84
    @51
    @82
    @68
    cM
    zaddcl
    expcom
    syl
    ad2antrl
    syl5com
    impcom
    @1
    @2
    @82
    df-3an
    sylanbrc
    cA
    cB
    @71
    cV
    ccatsymb
    syl
    @70
    @77
    @78
    @80
    @69
    @16
    @77
    wn
    #
    @69
    @68
    cn0
    wcel
    #
    @16
    @87
    @68
    @17
    elfzonn0
    @5
    @88
    @87
    wi
    #
    @3
    @9
    @5
    @56
    @89
    @57
    @55
    @52
    @89
    @53
    @52
    @89
    wi
    @54
    @52
    @53
    @89
    @49
    @51
    @53
    @89
    wi
    @50
    @49
    @51
    wa
    #
    @88
    @53
    @87
    @90
    @88
    @53
    @87
    wi
    @90
    @88
    wa
    @53
    @71
    cL
    clt
    wbr
    #
    wn
    #
    @87
    @90
    cL
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    wa
    #
    @88
    @53
    @92
    wi
    #
    @49
    @93
    @51
    @94
    cL
    zre
    cM
    zre
    anim12i
    @88
    @84
    cc0
    @68
    cle
    wbr
    #
    wa
    @95
    @96
    wi
    #
    @68
    elnn0z
    @84
    @68
    cr
    wcel
    #
    @97
    @98
    @68
    zre
    @97
    @99
    @95
    @96
    @99
    @95
    wa
    #
    @97
    @96
    @100
    @97
    @53
    @92
    @100
    @97
    @53
    wa
    #
    cL
    @71
    cle
    wbr
    #
    @92
    @100
    @101
    cc0
    cL
    caddc
    co
    #
    @71
    cle
    wbr
    #
    @102
    @100
    cc0
    cr
    wcel
    #
    @93
    wa
    #
    @99
    @94
    wa
    #
    @101
    @104
    wi
    @95
    @106
    @99
    @94
    @93
    @106
    @94
    @105
    @93
    @94
    0red
    anim1i
    ancoms
    adantl
    @95
    @94
    @99
    @93
    @94
    simpr
    anim2i
    #
    cc0
    cL
    @68
    cM
    le2add
    syl2anc
    @100
    @103
    cL
    @71
    cle
    @93
    @103
    cL
    wceq
    @99
    @94
    @93
    cL
    cL
    recn
    addid2d
    ad2antrl
    breq1d
    sylibd
    @100
    cL
    @71
    @95
    @93
    @99
    @93
    @94
    simpl
    adantl
    @100
    @107
    @71
    cr
    wcel
    @108
    @68
    cM
    readdcl
    syl
    lenltd
    sylibd
    expd
    com12
    expd
    mpan9
    sylbi
    mpan9
    @77
    @91
    @24
    cL
    @71
    clt
    cL
    @24
    swrdccatin12.l
    eqcomi
    breq2i
    notbii
    syl6ibr
    ex
    com23
    3adant2
    com12
    adantr
    impcom
    sylbi
    ad2antrl
    syl5com
    impcom
    iffalsed
    @70
    @79
    @73
    cB
    @69
    @16
    @79
    @73
    wceq
    #
    @69
    @84
    @16
    @109
    @85
    @5
    @84
    @109
    wi
    #
    @3
    @9
    @5
    @56
    @110
    @57
    @52
    @110
    @55
    @49
    @51
    @110
    @50
    @90
    @84
    @109
    @34
    @90
    @84
    wa
    #
    @109
    wi
    swrdccatin12.l
    @111
    @71
    cL
    cmin
    co
    #
    @73
    wceq
    @34
    @109
    @111
    @68
    cM
    cL
    @84
    @68
    cc
    wcel
    @90
    @68
    zcn
    adantl
    @90
    @46
    @84
    @51
    @46
    @49
    @58
    adantl
    adantr
    @49
    @47
    @51
    @84
    @59
    ad2antrr
    addsubassd
    @34
    @112
    @79
    @73
    cL
    @24
    @71
    cmin
    oveq2
    eqeq1d
    syl5ib
    ax-mp
    ex
    3adant2
    adantr
    sylbi
    ad2antrl
    syl5com
    impcom
    fveq2d
    3eqtrd
    @70
    @11
    @0
    wcel
    #
    @23
    cN
    cc0
    @11
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @68
    @20
    wcel
    #
    @75
    @72
    wceq
    @3
    @113
    @10
    @69
    cV
    cA
    cB
    ccatcl
    ad2antrr
    @16
    @23
    @69
    @10
    @3
    @23
    @5
    @3
    @23
    wi
    @9
    @3
    @5
    @23
    @1
    @5
    @23
    wi
    @2
    @1
    @4
    @22
    cM
    @1
    @37
    cL
    @39
    wcel
    @4
    @22
    wss
    @38
    @37
    cL
    @24
    @39
    swrdccatin12.l
    @41
    syl5eqel
    cL
    cc0
    cN
    fzss1
    3syl
    sseld
    adantr
    com12
    adantr
    impcom
    adantr
    @16
    @116
    @69
    @10
    @3
    @116
    @9
    @3
    @116
    wi
    #
    @5
    @9
    @32
    @118
    @34
    @9
    @32
    wb
    swrdccatin12.l
    @35
    ax-mp
    @32
    @3
    @116
    @32
    @3
    wa
    @116
    @27
    @3
    @32
    @27
    @3
    @31
    @26
    cN
    @3
    @40
    @42
    @1
    @40
    @2
    @1
    @37
    @40
    @38
    @41
    syl
    adantr
    @43
    syl
    sseld
    impcom
    @3
    @116
    @27
    wb
    @32
    @3
    @115
    @26
    cN
    @3
    @114
    @25
    cc0
    cfz
    cV
    cA
    cB
    ccatlen
    oveq2d
    eleq2d
    adantl
    mpbird
    ex
    sylbi
    adantl
    impcom
    adantr
    @16
    @69
    @117
    @5
    @69
    @117
    wi
    @3
    @9
    @5
    @69
    @117
    @5
    @18
    @20
    @68
    @5
    @17
    @19
    cc0
    cfzo
    cL
    cM
    cN
    fzmmmeqm
    oveq2d
    eleq2d
    biimpd
    ad2antrl
    imp
    cV
    @11
    cM
    cN
    @68
    swrdfv
    syl31anc
    @16
    @2
    @60
    @61
    w3a
    @69
    @76
    @74
    wceq
    @16
    @2
    @60
    @61
    @62
    @63
    @10
    @3
    @61
    @9
    @64
    @5
    @3
    @9
    @61
    @2
    @9
    @61
    wi
    #
    @1
    @2
    @65
    @119
    @67
    @66
    syl
    adantl
    com12
    adantl
    impcom
    3jca
    cV
    cB
    @13
    @14
    @68
    swrdfv
    sylan
    3eqtr4d
    eqfnfvd
    ex
end
