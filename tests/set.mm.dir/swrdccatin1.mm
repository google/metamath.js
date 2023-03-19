include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "cconcat.mm"
include "cop.mm"
include "csubstr.mm"
include "wi.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "elfz1eq.mm"
include "c0.mm"
include "swrd00.mm"
include "eqtr4i.mm"
include "opeq1.mm"
include "oveq2d.mm"
include "3eqtr4a.mm"
include "syl.mm"
include "opeq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "syl6bi.mm"
include "com23.mm"
include "impd.mm"
include "a1d.mm"
include "wn.mm"
include "cmin.mm"
include "cfzo.mm"
include "wfn.mm"
include "ccatcl.mm"
include "adantl.mm"
include "adantr.mm"
include "simprl.mm"
include "elfzelfzccat.mm"
include "com12.mm"
include "impcom.mm"
include "swrdvalfn.mm"
include "syl3anc.mm"
include "w3a.mm"
include "3anass.mm"
include "simplbi2.mm"
include "ad2antrl.mm"
include "imp.mm"
include "cv.mm"
include "caddc.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "cn0.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "elfzo0.mm"
include "cle.mm"
include "elfz2nn0.mm"
include "nn0addcl.mm"
include "expcom.mm"
include "3ad2ant1.mm"
include "sylbi.mm"
include "lencl.mm"
include "wne.mm"
include "df-ne.mm"
include "elnnne0.mm"
include "syl5bir.mm"
include "cr.mm"
include "nn0re.mm"
include "ltaddsubd.mm"
include "ltletr.mm"
include "expd.mm"
include "sylbird.mm"
include "ex.mm"
include "com24.mm"
include "3impia.mm"
include "com13.mm"
include "impancom.mm"
include "3adant2.mm"
include "a1i.mm"
include "imp32.mm"
include "syl5bi.mm"
include "syl3anbrc.mm"
include "ccatval1.mm"
include "3jca.mm"
include "swrdfv.mm"
include "sylancom.mm"
include "sylan.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"
include "pm2.61i.mm"

theorem swrdccatin1
  let cA: class A
  let cB: class B
  let cM: class M
  let cN: class N
  let cV: class V
  let vk: setvar k


  assert |- ( ( A e. Word V /\ B e. Word V ) -> ( ( M e. ( 0 ... N ) /\ N e. ( 0 ... ( # ` A ) ) ) -> ( ( A ++ B ) substr <. M , N >. ) = ( A substr <. M , N >. ) ) )

  proof
    cA
    chash
    cfv
    #
    cc0
    wceq
    #
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @2
    wcel
    #
    wa
    #
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
    @0
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
    #
    csubstr
    co
    #
    cA
    @12
    csubstr
    co
    #
    wceq
    #
    wi
    #
    wi
    @1
    @16
    @5
    @1
    @7
    @9
    @15
    @1
    @9
    @7
    @15
    @1
    @9
    cN
    cc0
    cc0
    cfz
    co
    #
    wcel
    #
    @7
    @15
    wi
    #
    @1
    @8
    @17
    cN
    @0
    cc0
    cc0
    cfz
    oveq2
    eleq2d
    @18
    cN
    cc0
    wceq
    #
    @19
    cN
    cc0
    elfz1eq
    @20
    @19
    cM
    @17
    wcel
    #
    @11
    cM
    cc0
    cop
    #
    csubstr
    co
    #
    cA
    @22
    csubstr
    co
    #
    wceq
    #
    wi
    @21
    cM
    cc0
    wceq
    #
    @25
    cM
    cc0
    elfz1eq
    @26
    @11
    cc0
    cc0
    cop
    #
    csubstr
    co
    #
    cA
    @27
    csubstr
    co
    #
    @23
    @24
    @28
    c0
    @29
    @11
    cc0
    swrd00
    cA
    cc0
    swrd00
    eqtr4i
    @26
    @22
    @27
    @11
    csubstr
    cM
    cc0
    cc0
    opeq1
    #
    oveq2d
    @26
    @22
    @27
    cA
    csubstr
    @30
    oveq2d
    3eqtr4a
    syl
    @20
    @7
    @21
    @15
    @25
    @20
    @6
    @17
    cM
    cN
    cc0
    cc0
    cfz
    oveq2
    eleq2d
    @20
    @13
    @23
    @14
    @24
    @20
    @12
    @22
    @11
    csubstr
    cN
    cc0
    cM
    opeq2
    #
    oveq2d
    @20
    @12
    @22
    cA
    csubstr
    @31
    oveq2d
    eqeq12d
    imbi12d
    mpbiri
    syl
    syl6bi
    com23
    impd
    a1d
    @1
    wn
    #
    @5
    @16
    @32
    @5
    wa
    #
    @10
    @15
    @33
    @10
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
    @13
    @14
    @34
    @11
    @2
    wcel
    #
    @7
    cN
    cc0
    @11
    chash
    cfv
    cfz
    co
    wcel
    #
    @13
    @36
    wfn
    @33
    @37
    @10
    @5
    @37
    @32
    cV
    cA
    cB
    ccatcl
    adantl
    #
    adantr
    @33
    @7
    @9
    simprl
    #
    @10
    @33
    @38
    @9
    @33
    @38
    wi
    @7
    @33
    @9
    @38
    @5
    @9
    @38
    wi
    @32
    cA
    cB
    cN
    cV
    elfzelfzccat
    adantl
    com12
    adantl
    impcom
    #
    @11
    cM
    cN
    cV
    swrdvalfn
    syl3anc
    @34
    @3
    @7
    @9
    w3a
    #
    @14
    @36
    wfn
    @33
    @10
    @42
    @3
    @10
    @42
    wi
    @32
    @4
    @42
    @3
    @10
    @3
    @7
    @9
    3anass
    simplbi2
    ad2antrl
    imp
    #
    cA
    cM
    cN
    cV
    swrdvalfn
    syl
    @34
    vk
    cv
    #
    @36
    wcel
    #
    wa
    #
    @44
    cM
    caddc
    co
    #
    @11
    cfv
    #
    @47
    cA
    cfv
    #
    @44
    @13
    cfv
    #
    @44
    @14
    cfv
    #
    @46
    @3
    @4
    @47
    cc0
    @0
    cfzo
    co
    wcel
    #
    @48
    @49
    wceq
    @33
    @3
    @10
    @45
    @32
    @3
    @4
    simprl
    ad2antrr
    @33
    @4
    @10
    @45
    @32
    @3
    @4
    simprr
    ad2antrr
    @46
    @47
    cn0
    wcel
    #
    @0
    cn
    wcel
    #
    @47
    @0
    clt
    wbr
    #
    @52
    @45
    @34
    @53
    @45
    @44
    cn0
    wcel
    #
    @35
    cn
    wcel
    #
    @44
    @35
    clt
    wbr
    #
    w3a
    #
    @34
    @53
    wi
    #
    @44
    @35
    elfzo0
    #
    @56
    @57
    @60
    @58
    @34
    @56
    @53
    @7
    @56
    @53
    wi
    #
    @33
    @9
    @7
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    @62
    cM
    cN
    elfz2nn0
    #
    @63
    @64
    @62
    @65
    @56
    @63
    @53
    @44
    cM
    nn0addcl
    #
    expcom
    3ad2ant1
    sylbi
    ad2antrl
    com12
    3ad2ant1
    sylbi
    impcom
    @33
    @54
    @10
    @45
    @5
    @32
    @54
    @3
    @32
    @54
    wi
    #
    @4
    @3
    @0
    cn0
    wcel
    #
    @69
    cV
    cA
    lencl
    @32
    @0
    cc0
    wne
    #
    @70
    @54
    @0
    cc0
    df-ne
    @54
    @70
    @71
    @0
    elnnne0
    simplbi2
    syl5bir
    syl
    adantr
    impcom
    ad2antrr
    @34
    @45
    @55
    @45
    @59
    @34
    @55
    @61
    @33
    @7
    @9
    @59
    @55
    wi
    #
    @7
    @9
    @72
    wi
    #
    wi
    @33
    @7
    @66
    @73
    @67
    @63
    @64
    @73
    @65
    @9
    @63
    @72
    @9
    @64
    @70
    cN
    @0
    cle
    wbr
    #
    w3a
    #
    @63
    @72
    wi
    cN
    @0
    elfz2nn0
    @59
    @63
    @75
    @55
    @56
    @58
    @63
    @75
    @55
    wi
    #
    wi
    @57
    @56
    @63
    @58
    @76
    @75
    @58
    @56
    @63
    wa
    #
    @55
    @64
    @70
    @74
    @58
    @77
    @55
    wi
    wi
    @64
    @70
    wa
    #
    @77
    @58
    @74
    @55
    @78
    @77
    @58
    @74
    @55
    wi
    #
    wi
    @78
    @77
    wa
    #
    @58
    @47
    cN
    clt
    wbr
    #
    @79
    @80
    @44
    cM
    cN
    @56
    @44
    cr
    wcel
    @78
    @63
    @44
    nn0re
    ad2antrl
    @77
    cM
    cr
    wcel
    #
    @78
    @63
    @82
    @56
    cM
    nn0re
    adantl
    adantl
    @64
    cN
    cr
    wcel
    #
    @70
    @77
    cN
    nn0re
    ad2antrr
    #
    ltaddsubd
    @80
    @81
    @74
    @55
    @80
    @47
    cr
    wcel
    #
    @83
    @0
    cr
    wcel
    #
    @81
    @74
    wa
    @55
    wi
    @77
    @85
    @78
    @77
    @53
    @85
    @68
    @47
    nn0re
    syl
    adantl
    @84
    @78
    @86
    @77
    @70
    @86
    @64
    @0
    nn0re
    adantl
    adantr
    @47
    cN
    @0
    ltletr
    syl3anc
    expd
    sylbird
    ex
    com24
    3impia
    com13
    impancom
    3adant2
    com13
    sylbi
    com12
    3ad2ant1
    sylbi
    a1i
    imp32
    syl5bi
    imp
    @47
    @0
    elfzo0
    syl3anbrc
    cV
    cA
    cB
    @47
    ccatval1
    syl3anc
    @34
    @45
    @37
    @7
    @38
    w3a
    @50
    @48
    wceq
    @46
    @37
    @7
    @38
    @33
    @37
    @10
    @45
    @39
    ad2antrr
    @34
    @7
    @45
    @40
    adantr
    @34
    @38
    @45
    @41
    adantr
    3jca
    cV
    @11
    cM
    cN
    @44
    swrdfv
    sylancom
    @34
    @42
    @45
    @51
    @49
    wceq
    @43
    cV
    cA
    cM
    cN
    @44
    swrdfv
    sylan
    3eqtr4d
    eqfnfvd
    ex
    ex
    pm2.61i
end
