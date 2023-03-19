include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cn.mm"
include "cgcd.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "wa.mm"
include "cmo.mm"
include "cmul.mm"
include "wi.mm"
include "cc0.mm"
include "zcn.mm"
include "mul01d.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "wne.mm"
include "cv.mm"
include "cmin.mm"
include "wrex.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "adantl.mm"
include "simpl.mm"
include "simp3.mm"
include "divgcdnnr.mm"
include "syl2anr.mm"
include "simpl1.mm"
include "simpl2.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "nnzd.mm"
include "zsubcl.mm"
include "3adant3.mm"
include "jca.mm"
include "divides.mm"
include "syl.mm"
include "3bitrd.mm"
include "simpr.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "cc.mm"
include "ad3antrrr.mm"
include "mulcan2d.mm"
include "subdir.mm"
include "syl3an.mm"
include "eqeq2d.mm"
include "bitr3d.mm"
include "nnz.mm"
include "cn0.mm"
include "anim12i.mm"
include "gcdcl.mm"
include "nn0cnd.mm"
include "wn.mm"
include "nnne0.mm"
include "neneqd.mm"
include "intnand.mm"
include "gcdeq0.mm"
include "necon3abid.mm"
include "mpbird.mm"
include "divassd.mm"
include "3anass.mm"
include "sylibr.mm"
include "divgcdz.mm"
include "eqeltrd.mm"
include "dvdsmul1.mm"
include "syl2an2.mm"
include "nncnd.mm"
include "divmulasscom.mm"
include "syl32anc.mm"
include "breqtrrd.mm"
include "exp32.mm"
include "adantrd.mm"
include "imp.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "zmulcl.mm"
include "3adant2.mm"
include "3adant1.mm"
include "sylibrd.mm"
include "ex.mm"
include "com23.mm"
include "com12.mm"
include "pm2.61ine.mm"

theorem cncongr2
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cN: class N
  let vk: setvar k


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( N e. NN /\ M = ( N / ( C gcd N ) ) ) ) -> ( ( A mod M ) = ( B mod M ) -> ( ( A x. C ) mod N ) = ( ( B x. C ) mod N ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    w3a
    #
    cN
    cn
    wcel
    #
    cM
    cN
    cC
    cN
    cgcd
    co
    #
    cdiv
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    cA
    cM
    cmo
    co
    #
    cB
    cM
    cmo
    co
    #
    wceq
    #
    cA
    cC
    cmul
    co
    #
    cN
    cmo
    co
    #
    cB
    cC
    cmul
    co
    #
    cN
    cmo
    co
    #
    wceq
    #
    @9
    @12
    wa
    #
    @17
    wi
    cC
    cc0
    @18
    @17
    cC
    cc0
    wceq
    #
    cA
    cc0
    cmul
    co
    #
    cN
    cmo
    co
    #
    cB
    cc0
    cmul
    co
    #
    cN
    cmo
    co
    #
    wceq
    #
    @9
    @24
    @12
    @9
    @20
    @22
    cN
    cmo
    @3
    @20
    @22
    wceq
    @8
    @3
    @20
    cc0
    @22
    @0
    @1
    @20
    cc0
    wceq
    @2
    @0
    cA
    cA
    zcn
    #
    mul01d
    3ad2ant1
    @1
    @0
    @22
    cc0
    wceq
    @2
    @1
    cB
    cB
    zcn
    #
    mul01d
    3ad2ant2
    eqtr4d
    adantr
    oveq1d
    adantr
    @19
    @14
    @21
    @16
    @23
    @19
    @13
    @20
    cN
    cmo
    cC
    cc0
    cA
    cmul
    oveq2
    oveq1d
    @19
    @15
    @22
    cN
    cmo
    cC
    cc0
    cB
    cmul
    oveq2
    oveq1d
    eqeq12d
    syl5ibr
    @18
    cC
    cc0
    wne
    #
    @17
    @9
    @12
    @27
    @17
    wi
    #
    @9
    @12
    vk
    cv
    #
    @6
    cmul
    co
    #
    cA
    cB
    cmin
    co
    #
    wceq
    #
    vk
    cz
    wrex
    #
    @28
    @9
    @12
    cA
    @6
    cmo
    co
    #
    cB
    @6
    cmo
    co
    #
    wceq
    #
    @6
    @31
    cdvds
    wbr
    #
    @33
    @8
    @12
    @36
    wb
    #
    @3
    @7
    @38
    @4
    @7
    @10
    @34
    @11
    @35
    cM
    @6
    cA
    cmo
    oveq2
    cM
    @6
    cB
    cmo
    oveq2
    eqeq12d
    adantl
    adantl
    @9
    @6
    cn
    wcel
    #
    @0
    @1
    @36
    @37
    wb
    @8
    @4
    @2
    @39
    @3
    @4
    @7
    simpl
    #
    @0
    @1
    @2
    simp3
    #
    cN
    cC
    divgcdnnr
    syl2anr
    #
    @0
    @1
    @2
    @8
    simpl1
    @0
    @1
    @2
    @8
    simpl2
    cA
    cB
    @6
    moddvds
    syl3anc
    @9
    @6
    cz
    wcel
    #
    @31
    cz
    wcel
    #
    wa
    @37
    @33
    wb
    @9
    @43
    @44
    @9
    @6
    @42
    nnzd
    #
    @3
    @44
    @8
    @0
    @1
    @44
    @2
    cA
    cB
    zsubcl
    #
    3adant3
    adantr
    jca
    vk
    @6
    @31
    divides
    syl
    3bitrd
    @9
    @27
    @33
    @17
    @9
    @27
    @33
    @17
    wi
    @9
    @27
    wa
    #
    @33
    cN
    @13
    @15
    cmin
    co
    #
    cdvds
    wbr
    #
    @17
    @47
    @32
    @49
    vk
    cz
    @47
    @29
    cz
    wcel
    #
    wa
    #
    @32
    @30
    cC
    cmul
    co
    #
    @48
    wceq
    #
    @49
    @51
    @52
    @31
    cC
    cmul
    co
    #
    wceq
    @32
    @53
    @51
    @30
    @31
    cC
    @51
    @30
    @51
    @29
    @6
    @47
    @50
    simpr
    @47
    @43
    @50
    @9
    @43
    @27
    @45
    adantr
    adantr
    zmulcld
    zcnd
    @3
    @31
    cc
    wcel
    #
    @8
    @27
    @50
    @0
    @1
    @55
    @2
    @0
    @1
    wa
    @31
    @46
    zcnd
    3adant3
    ad3antrrr
    @3
    cC
    cc
    wcel
    #
    @8
    @27
    @50
    @3
    cC
    @41
    zcnd
    #
    ad3antrrr
    @47
    @27
    @50
    @9
    @27
    simpr
    adantr
    mulcan2d
    @51
    @54
    @48
    @52
    @3
    @54
    @48
    wceq
    #
    @8
    @27
    @50
    @0
    cA
    cc
    wcel
    @1
    cB
    cc
    wcel
    @2
    @56
    @58
    @25
    @26
    cC
    zcn
    cA
    cB
    cC
    subdir
    syl3an
    ad3antrrr
    eqeq2d
    bitr3d
    @51
    cN
    @52
    cdvds
    wbr
    #
    @53
    @49
    @47
    @50
    @59
    @9
    @50
    @59
    wi
    #
    @27
    @3
    @8
    @60
    @3
    @4
    @60
    @7
    @3
    @4
    @50
    @59
    @3
    @4
    @50
    wa
    #
    wa
    #
    cN
    cN
    @29
    cC
    cmul
    co
    @5
    cdiv
    co
    #
    cmul
    co
    #
    @52
    cdvds
    @61
    cN
    cz
    wcel
    #
    @3
    @63
    cz
    wcel
    cN
    @64
    cdvds
    wbr
    @4
    @65
    @50
    cN
    nnz
    #
    adantr
    @62
    @63
    @29
    cC
    @5
    cdiv
    co
    #
    cmul
    co
    cz
    @62
    @29
    cC
    @5
    @61
    @29
    cc
    wcel
    #
    @3
    @61
    @29
    @4
    @50
    simpr
    #
    zcnd
    adantl
    #
    @3
    @56
    @61
    @57
    adantr
    #
    @62
    @5
    @62
    @2
    @65
    wa
    #
    @5
    cn0
    wcel
    @3
    @2
    @61
    @65
    @41
    @61
    cN
    @4
    @50
    simpl
    #
    nnzd
    anim12i
    #
    cC
    cN
    gcdcl
    syl
    nn0cnd
    #
    @62
    @5
    cc0
    wne
    #
    @19
    cN
    cc0
    wceq
    #
    wa
    #
    wn
    @62
    @77
    @19
    @61
    @77
    wn
    #
    @3
    @4
    @79
    @50
    @4
    cN
    cc0
    cN
    nnne0
    #
    neneqd
    adantr
    adantl
    intnand
    @62
    @78
    @5
    cc0
    @62
    @72
    @5
    cc0
    wceq
    @78
    wb
    @74
    cC
    cN
    gcdeq0
    syl
    necon3abid
    mpbird
    #
    divassd
    @62
    @29
    @67
    @61
    @50
    @3
    @69
    adantl
    @62
    @2
    @65
    cN
    cc0
    wne
    #
    w3a
    #
    @67
    cz
    wcel
    @62
    @2
    @65
    @82
    wa
    #
    wa
    @83
    @3
    @2
    @61
    @84
    @41
    @4
    @84
    @50
    @4
    @65
    @82
    @66
    @80
    jca
    adantr
    anim12i
    @2
    @65
    @82
    3anass
    sylibr
    cC
    cN
    divgcdz
    syl
    zmulcld
    eqeltrd
    cN
    @63
    dvdsmul1
    syl2an2
    @62
    @68
    cN
    cc
    wcel
    #
    @56
    @5
    cc
    wcel
    @76
    @52
    @64
    wceq
    @70
    @61
    @85
    @3
    @61
    cN
    @73
    nncnd
    adantl
    @71
    @75
    @81
    @29
    cN
    cC
    @5
    divmulasscom
    syl32anc
    breqtrrd
    exp32
    adantrd
    imp
    adantr
    imp
    @52
    @48
    cN
    cdvds
    breq2
    syl5ibcom
    sylbid
    rexlimdva
    @9
    @17
    @49
    wb
    #
    @27
    @9
    @4
    @13
    cz
    wcel
    #
    @15
    cz
    wcel
    #
    @86
    @8
    @4
    @3
    @40
    adantl
    @3
    @87
    @8
    @0
    @2
    @87
    @1
    cA
    cC
    zmulcl
    3adant2
    adantr
    @3
    @88
    @8
    @1
    @2
    @88
    @0
    cB
    cC
    zmulcl
    3adant1
    adantr
    @13
    @15
    cN
    moddvds
    syl3anc
    adantr
    sylibrd
    ex
    com23
    sylbid
    imp
    com12
    pm2.61ine
    ex
end
