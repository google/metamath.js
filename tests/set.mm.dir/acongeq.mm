include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "w3a.mm"
include "wceq.mm"
include "c2.mm"
include "cmul.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "wo.mm"
include "wa.mm"
include "cz.mm"
include "2z.mm"
include "nnz.mm"
include "3ad2ant1.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "elfzelz.mm"
include "3ad2ant2.mm"
include "congid.mm"
include "syl2anc.mm"
include "adantr.mm"
include "oveq2.mm"
include "adantl.mm"
include "breqtrd.mm"
include "orcd.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "3ad2ant3.mm"
include "zsubcld.mm"
include "zcnd.mm"
include "abscld.mm"
include "cr.mm"
include "nnre.mm"
include "0re.mm"
include "resubcl.mm"
include "sylancl.mm"
include "2re.mm"
include "remulcl.mm"
include "cle.mm"
include "simp2.mm"
include "simp3.mm"
include "leidd.mm"
include "fzmaxdif.mm"
include "syl221anc.mm"
include "caddc.mm"
include "crp.mm"
include "nnrp.mm"
include "ltaddrpd.mm"
include "recnd.mm"
include "subid1d.mm"
include "2timesd.mm"
include "3brtr4d.mm"
include "lelttrd.mm"
include "wb.mm"
include "2nn.mm"
include "simpl1.mm"
include "nnmulcl.mm"
include "simpl2.mm"
include "syl.mm"
include "simpl3.mm"
include "simpr.mm"
include "congabseq.mm"
include "syl31anc.mm"
include "mpbid.mm"
include "c1.mm"
include "simpll2.mm"
include "elfzle1.mm"
include "zred.mm"
include "renegcld.mm"
include "resubcld.mm"
include "ad2antrr.mm"
include "1re.mm"
include "znegcld.mm"
include "abssubd.mm"
include "0zd.mm"
include "1z.mm"
include "zsubcl.mm"
include "fzneg.mm"
include "syl3anc.mm"
include "neg0.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "cn0.mm"
include "simp1.mm"
include "nnm1nn0.mm"
include "nn0ge0d.mm"
include "0m0e0.mm"
include "1cnd.mm"
include "addsubassd.mm"
include "oveq1d.mm"
include "cc.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "subnegd.mm"
include "3eqtr4rd.mm"
include "eqbrtrd.mm"
include "ltm1d.mm"
include "simplr.mm"
include "le0neg1d.mm"
include "mpbird.mm"
include "letri3.mm"
include "mpbir2and.mm"
include "negeqd.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "eqbrtrrd.mm"
include "ppncand.mm"
include "addcomd.mm"
include "eqtr4d.mm"
include "breqtrrd.mm"
include "dvdsadd.mm"
include "cuz.mm"
include "nnnn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzm1.mm"
include "biimpa.mm"
include "mpjaodan.mm"
include "jaodan.mm"
include "impbida.mm"

theorem acongeq
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. NN /\ B e. ( 0 ... A ) /\ C e. ( 0 ... A ) ) -> ( B = C <-> ( ( 2 x. A ) || ( B - C ) \/ ( 2 x. A ) || ( B - -u C ) ) ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cc0
    cA
    cfz
    co
    #
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    #
    cB
    cC
    wceq
    #
    c2
    cA
    cmul
    co
    #
    cB
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    @6
    cB
    cC
    cneg
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    wo
    @4
    @5
    wa
    #
    @8
    @11
    @12
    @6
    cB
    cB
    cmin
    co
    #
    @7
    cdvds
    @4
    @6
    @13
    cdvds
    wbr
    #
    @5
    @4
    @6
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @14
    @4
    c2
    cz
    wcel
    cA
    cz
    wcel
    #
    @15
    2z
    @0
    @2
    @17
    @3
    cA
    nnz
    3ad2ant1
    #
    c2
    cA
    zmulcl
    sylancr
    #
    @2
    @0
    @16
    @3
    cB
    cc0
    cA
    elfzelz
    #
    3ad2ant2
    #
    @6
    cB
    congid
    syl2anc
    adantr
    @5
    @13
    @7
    wceq
    @4
    cB
    cC
    cB
    cmin
    oveq2
    adantl
    breqtrd
    orcd
    @4
    @8
    @5
    @11
    @4
    @8
    wa
    #
    @7
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    @5
    @4
    @24
    @8
    @4
    @23
    cA
    cc0
    cmin
    co
    #
    @6
    @4
    @7
    @4
    @7
    @4
    cB
    cC
    @21
    @3
    @0
    cC
    cz
    wcel
    #
    @2
    cC
    cc0
    cA
    elfzelz
    #
    3ad2ant3
    #
    zsubcld
    zcnd
    abscld
    @4
    cA
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @25
    cr
    wcel
    @0
    @2
    @29
    @3
    cA
    nnre
    3ad2ant1
    #
    0re
    cA
    cc0
    resubcl
    sylancl
    #
    @4
    c2
    cr
    wcel
    @29
    @6
    cr
    wcel
    #
    2re
    @31
    c2
    cA
    remulcl
    sylancr
    #
    @4
    @17
    @2
    @17
    @3
    @25
    @25
    cle
    wbr
    @23
    @25
    cle
    wbr
    @18
    @0
    @2
    @3
    simp2
    @18
    @0
    @2
    @3
    simp3
    #
    @4
    @25
    @32
    leidd
    cB
    cc0
    cA
    cC
    cc0
    cA
    fzmaxdif
    syl221anc
    @4
    cA
    cA
    cA
    caddc
    co
    #
    @25
    @6
    clt
    @4
    cA
    cA
    @31
    @0
    @2
    cA
    crp
    wcel
    @3
    cA
    nnrp
    3ad2ant1
    ltaddrpd
    @4
    cA
    @4
    cA
    @31
    recnd
    #
    subid1d
    @4
    cA
    @37
    2timesd
    #
    3brtr4d
    lelttrd
    #
    adantr
    @22
    @6
    cn
    wcel
    #
    @16
    @26
    @8
    @24
    @5
    wb
    @22
    c2
    cn
    wcel
    #
    @0
    @40
    2nn
    @0
    @2
    @3
    @8
    simpl1
    c2
    cA
    nnmulcl
    #
    sylancr
    @22
    @2
    @16
    @0
    @2
    @3
    @8
    simpl2
    @20
    syl
    @22
    @3
    @26
    @0
    @2
    @3
    @8
    simpl3
    @27
    syl
    @4
    @8
    simpr
    @6
    cB
    cC
    congabseq
    syl31anc
    mpbid
    @4
    @11
    wa
    #
    cC
    cc0
    cA
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    @5
    cC
    cA
    wceq
    #
    @43
    @45
    wa
    #
    @9
    cc0
    cB
    cC
    @47
    @9
    cc0
    cneg
    #
    cc0
    @47
    cC
    cc0
    @47
    cC
    cc0
    wceq
    #
    cC
    cc0
    cle
    wbr
    #
    cc0
    cC
    cle
    wbr
    #
    @47
    @50
    cc0
    @9
    cle
    wbr
    @47
    cc0
    cB
    @9
    cle
    @47
    @2
    cc0
    cB
    cle
    wbr
    @0
    @2
    @3
    @11
    @45
    simpll2
    #
    cB
    cc0
    cA
    elfzle1
    syl
    @47
    @10
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    cB
    @9
    wceq
    #
    @47
    @53
    cA
    @44
    cneg
    #
    cmin
    co
    #
    @6
    @4
    @53
    cr
    wcel
    @11
    @45
    @4
    @10
    @4
    @10
    @4
    cB
    @9
    @4
    cB
    @21
    zred
    @4
    cC
    @4
    cC
    @28
    zred
    renegcld
    resubcld
    recnd
    abscld
    ad2antrr
    @4
    @57
    cr
    wcel
    @11
    @45
    @4
    cA
    @56
    @31
    @4
    @44
    @4
    @29
    c1
    cr
    wcel
    @44
    cr
    wcel
    @31
    1re
    cA
    c1
    resubcl
    sylancl
    renegcld
    resubcld
    ad2antrr
    @4
    @33
    @11
    @45
    @34
    ad2antrr
    @47
    @53
    @9
    cB
    cmin
    co
    cabs
    cfv
    #
    @57
    cle
    @47
    cB
    @9
    @47
    cB
    @4
    @16
    @11
    @45
    @21
    ad2antrr
    #
    zcnd
    @47
    @9
    @4
    @9
    cz
    wcel
    #
    @11
    @45
    @4
    cC
    @28
    znegcld
    ad2antrr
    #
    zcnd
    abssubd
    @47
    cc0
    cz
    wcel
    #
    @9
    @56
    cc0
    cfz
    co
    #
    wcel
    @17
    @2
    cc0
    cc0
    cmin
    co
    #
    @57
    cle
    wbr
    #
    @58
    @57
    cle
    wbr
    @47
    0zd
    @47
    @9
    @56
    @48
    cfz
    co
    #
    @63
    @47
    @45
    @9
    @66
    wcel
    #
    @43
    @45
    simpr
    @4
    @45
    @67
    wb
    #
    @11
    @45
    @4
    @26
    @62
    @44
    cz
    wcel
    #
    @68
    @28
    @4
    0zd
    @4
    @17
    c1
    cz
    wcel
    @69
    @18
    1z
    cA
    c1
    zsubcl
    sylancl
    cC
    cc0
    @44
    fzneg
    syl3anc
    ad2antrr
    mpbid
    @47
    @48
    cc0
    @56
    cfz
    @48
    cc0
    wceq
    @47
    neg0
    a1i
    #
    oveq2d
    eleqtrd
    @4
    @17
    @11
    @45
    @18
    ad2antrr
    @52
    @4
    @65
    @11
    @45
    @4
    cc0
    @6
    c1
    cmin
    co
    #
    @64
    @57
    cle
    @4
    @71
    @4
    @40
    @71
    cn0
    wcel
    @4
    @41
    @0
    @40
    2nn
    @0
    @2
    @3
    simp1
    @42
    sylancr
    #
    @6
    nnm1nn0
    syl
    nn0ge0d
    @64
    cc0
    wceq
    @4
    0m0e0
    a1i
    @4
    @36
    c1
    cmin
    co
    cA
    @44
    caddc
    co
    @71
    @57
    @4
    cA
    cA
    c1
    @37
    @37
    @4
    1cnd
    addsubassd
    @4
    @6
    @36
    c1
    cmin
    @38
    oveq1d
    @4
    cA
    @44
    @37
    @4
    cA
    cc
    wcel
    c1
    cc
    wcel
    @44
    cc
    wcel
    @37
    ax-1cn
    cA
    c1
    subcl
    sylancl
    subnegd
    3eqtr4rd
    #
    3brtr4d
    ad2antrr
    @9
    @56
    cc0
    cB
    cc0
    cA
    fzmaxdif
    syl221anc
    eqbrtrd
    @4
    @57
    @6
    clt
    wbr
    @11
    @45
    @4
    @57
    @71
    @6
    clt
    @73
    @4
    @6
    @34
    ltm1d
    eqbrtrd
    ad2antrr
    lelttrd
    @47
    @40
    @16
    @60
    @11
    @54
    @55
    wb
    @4
    @40
    @11
    @45
    @72
    ad2antrr
    @59
    @61
    @4
    @11
    @45
    simplr
    @6
    cB
    @9
    congabseq
    syl31anc
    mpbid
    #
    breqtrd
    @47
    cC
    @45
    cC
    cr
    wcel
    #
    @43
    @45
    cC
    cC
    cc0
    @44
    elfzelz
    zred
    adantl
    #
    le0neg1d
    mpbird
    @45
    @51
    @43
    cC
    cc0
    @44
    elfzle1
    adantl
    @47
    @75
    @30
    @49
    @50
    @51
    wa
    wb
    @76
    0re
    cC
    cc0
    letri3
    sylancl
    mpbir2and
    #
    negeqd
    @70
    eqtrd
    @74
    @77
    3eqtr4d
    @43
    @46
    wa
    #
    cB
    cA
    cC
    @78
    cB
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    cB
    cA
    wceq
    #
    @78
    @23
    @80
    @6
    clt
    @78
    @7
    @79
    cabs
    @46
    @7
    @79
    wceq
    @43
    cC
    cA
    cB
    cmin
    oveq2
    adantl
    fveq2d
    @4
    @24
    @11
    @46
    @39
    ad2antrr
    eqbrtrrd
    @78
    @40
    @16
    @17
    @6
    @79
    cdvds
    wbr
    #
    @81
    @82
    wb
    @4
    @40
    @11
    @46
    @72
    ad2antrr
    @4
    @16
    @11
    @46
    @21
    ad2antrr
    @4
    @17
    @11
    @46
    @18
    ad2antrr
    @78
    @83
    @6
    @6
    @79
    caddc
    co
    #
    cdvds
    wbr
    #
    @78
    @6
    @10
    @84
    cdvds
    @4
    @11
    @46
    simplr
    @78
    @36
    @79
    caddc
    co
    #
    cB
    cC
    caddc
    co
    #
    @84
    @10
    @78
    @86
    cB
    cA
    caddc
    co
    #
    @87
    @4
    @86
    @88
    wceq
    @11
    @46
    @4
    @86
    cA
    cB
    caddc
    co
    @88
    @4
    cA
    cA
    cB
    @37
    @37
    @4
    cB
    @21
    zcnd
    #
    ppncand
    @4
    cA
    cB
    @37
    @89
    addcomd
    eqtrd
    ad2antrr
    @46
    @87
    @88
    wceq
    @43
    cC
    cA
    cB
    caddc
    oveq2
    adantl
    eqtr4d
    @4
    @84
    @86
    wceq
    @11
    @46
    @4
    @6
    @36
    @79
    caddc
    @38
    oveq1d
    ad2antrr
    @4
    @10
    @87
    wceq
    @11
    @46
    @4
    cB
    cC
    @89
    @4
    cC
    @28
    zcnd
    subnegd
    ad2antrr
    3eqtr4d
    breqtrrd
    @78
    @15
    @79
    cz
    wcel
    #
    @83
    @85
    wb
    @4
    @15
    @11
    @46
    @19
    ad2antrr
    @4
    @90
    @11
    @46
    @4
    cB
    cA
    @21
    @18
    zsubcld
    ad2antrr
    @6
    @79
    dvdsadd
    syl2anc
    mpbird
    @6
    cB
    cA
    congabseq
    syl31anc
    mpbid
    @43
    @46
    simpr
    eqtr4d
    @4
    @45
    @46
    wo
    #
    @11
    @4
    cA
    cc0
    cuz
    cfv
    #
    wcel
    #
    @3
    @91
    @4
    cA
    cn0
    @92
    @0
    @2
    cA
    cn0
    wcel
    @3
    cA
    nnnn0
    3ad2ant1
    nn0uz
    syl6eleq
    @35
    @93
    @3
    @91
    cC
    cc0
    cA
    fzm1
    biimpa
    syl2anc
    adantr
    mpjaodan
    jaodan
    impbida
end
