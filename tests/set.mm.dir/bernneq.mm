include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cexp.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "cc.mm"
include "recn.mm"
include "mul01.mm"
include "1p0e1.mm"
include "syl6eq.mm"
include "1le1.mm"
include "ax-1cn.mm"
include "addcl.mm"
include "mpan.mm"
include "exp0.mm"
include "syl.mm"
include "syl5breqr.mm"
include "eqbrtrd.mm"
include "adantr.mm"
include "1re.mm"
include "nn0re.mm"
include "remulcl.mm"
include "sylan2.mm"
include "readdcl.mm"
include "sylancr.mm"
include "simpl.mm"
include "syl2anc.mm"
include "remulcld.mm"
include "reexpcl.mm"
include "sylan.mm"
include "anidms.mm"
include "msqge0.mm"
include "jca.mm"
include "nn0ge0.mm"
include "mulge0.mm"
include "syl2an.mm"
include "nn0cn.mm"
include "adantl.mm"
include "mul32d.mm"
include "breqtrd.mm"
include "addge01d.mm"
include "mpbid.mm"
include "mulcl.mm"
include "mulcld.mm"
include "addassd.mm"
include "muladd11.mm"
include "eqtr4d.mm"
include "wb.mm"
include "neg1rr.mm"
include "leadd2.mm"
include "mp3an13.mm"
include "1pneg1e0.mm"
include "breq1i.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "ad2ant2r.mm"
include "simprr.mm"
include "lemul1ad.mm"
include "letrd.mm"
include "adddi.mm"
include "mp3an3.mm"
include "mulid1.mm"
include "eqtrd.mm"
include "addass.mm"
include "mp3an1.mm"
include "expp1.mm"
include "3brtr4d.mm"
include "exp43.mm"
include "com12.mm"
include "impd.mm"
include "a2d.mm"
include "nn0ind.mm"
include "expd.mm"
include "3imp.mm"

theorem bernneq
  let cA: class A
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( A e. RR /\ N e. NN0 /\ -u 1 <_ A ) -> ( 1 + ( A x. N ) ) <_ ( ( 1 + A ) ^ N ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cn0
    wcel
    #
    c1
    cneg
    #
    cA
    cle
    wbr
    #
    c1
    cA
    cN
    cmul
    co
    #
    caddc
    co
    #
    c1
    cA
    caddc
    co
    #
    cN
    cexp
    co
    #
    cle
    wbr
    #
    @1
    @0
    @3
    @8
    wi
    @1
    @0
    @3
    @8
    @0
    @3
    wa
    #
    c1
    cA
    vj
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    @6
    @10
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @9
    c1
    cA
    cc0
    cmul
    co
    #
    caddc
    co
    #
    @6
    cc0
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @9
    c1
    cA
    vk
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    @6
    @19
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @9
    c1
    cA
    @19
    c1
    caddc
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @6
    @24
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @9
    @8
    wi
    vj
    vk
    cN
    @10
    cc0
    wceq
    #
    @14
    @18
    @9
    @29
    @12
    @16
    @13
    @17
    cle
    @29
    @11
    @15
    c1
    caddc
    @10
    cc0
    cA
    cmul
    oveq2
    oveq2d
    @10
    cc0
    @6
    cexp
    oveq2
    breq12d
    imbi2d
    @10
    @19
    wceq
    #
    @14
    @23
    @9
    @30
    @12
    @21
    @13
    @22
    cle
    @30
    @11
    @20
    c1
    caddc
    @10
    @19
    cA
    cmul
    oveq2
    oveq2d
    @10
    @19
    @6
    cexp
    oveq2
    breq12d
    imbi2d
    @10
    @24
    wceq
    #
    @14
    @28
    @9
    @31
    @12
    @26
    @13
    @27
    cle
    @31
    @11
    @25
    c1
    caddc
    @10
    @24
    cA
    cmul
    oveq2
    oveq2d
    @10
    @24
    @6
    cexp
    oveq2
    breq12d
    imbi2d
    @10
    cN
    wceq
    #
    @14
    @8
    @9
    @32
    @12
    @5
    @13
    @7
    cle
    @32
    @11
    @4
    c1
    caddc
    @10
    cN
    cA
    cmul
    oveq2
    oveq2d
    @10
    cN
    @6
    cexp
    oveq2
    breq12d
    imbi2d
    @0
    @18
    @3
    @0
    cA
    cc
    wcel
    #
    @18
    cA
    recn
    #
    @33
    @16
    c1
    @17
    cle
    @33
    @16
    c1
    cc0
    caddc
    co
    c1
    @33
    @15
    cc0
    c1
    caddc
    cA
    mul01
    oveq2d
    1p0e1
    syl6eq
    @33
    c1
    c1
    @17
    cle
    1le1
    @33
    @6
    cc
    wcel
    #
    @17
    c1
    wceq
    c1
    cc
    wcel
    #
    @33
    @35
    ax-1cn
    c1
    cA
    addcl
    #
    mpan
    @6
    exp0
    syl
    syl5breqr
    eqbrtrd
    syl
    adantr
    @19
    cn0
    wcel
    #
    @9
    @23
    @28
    @38
    @0
    @3
    @23
    @28
    wi
    #
    @0
    @38
    @3
    @39
    wi
    @0
    @38
    @3
    @23
    @28
    @0
    @38
    wa
    #
    @3
    @23
    wa
    #
    wa
    #
    @21
    cA
    caddc
    co
    #
    @22
    @6
    cmul
    co
    #
    @26
    @27
    cle
    @42
    @43
    @21
    @6
    cmul
    co
    #
    @44
    @40
    @43
    cr
    wcel
    #
    @41
    @40
    @21
    cr
    wcel
    #
    @0
    @46
    @40
    c1
    cr
    wcel
    #
    @20
    cr
    wcel
    #
    @47
    1re
    @38
    @0
    @19
    cr
    wcel
    #
    @49
    @19
    nn0re
    #
    cA
    @19
    remulcl
    #
    sylan2
    c1
    @20
    readdcl
    sylancr
    #
    @0
    @38
    simpl
    @21
    cA
    readdcl
    syl2anc
    #
    adantr
    @40
    @45
    cr
    wcel
    @41
    @40
    @21
    @6
    @53
    @0
    @6
    cr
    wcel
    #
    @38
    @48
    @0
    @55
    1re
    c1
    cA
    readdcl
    mpan
    #
    adantr
    #
    remulcld
    adantr
    @40
    @44
    cr
    wcel
    @41
    @40
    @22
    @6
    @0
    @55
    @38
    @22
    cr
    wcel
    #
    @56
    @6
    @19
    reexpcl
    sylan
    #
    @57
    remulcld
    adantr
    @40
    @43
    @45
    cle
    wbr
    @41
    @40
    @43
    @43
    @20
    cA
    cmul
    co
    #
    caddc
    co
    #
    @45
    cle
    @40
    cc0
    @60
    cle
    wbr
    @43
    @61
    cle
    wbr
    @40
    cc0
    cA
    cA
    cmul
    co
    #
    @19
    cmul
    co
    #
    @60
    cle
    @0
    @62
    cr
    wcel
    #
    cc0
    @62
    cle
    wbr
    #
    wa
    @50
    cc0
    @19
    cle
    wbr
    #
    wa
    cc0
    @63
    cle
    wbr
    @38
    @0
    @64
    @65
    @0
    @64
    cA
    cA
    remulcl
    anidms
    cA
    msqge0
    jca
    @38
    @50
    @66
    @51
    @19
    nn0ge0
    jca
    @62
    @19
    mulge0
    syl2an
    @40
    cA
    cA
    @19
    @0
    @33
    @38
    @34
    adantr
    #
    @67
    @38
    @19
    cc
    wcel
    #
    @0
    @19
    nn0cn
    #
    adantl
    mul32d
    breqtrd
    @40
    @43
    @60
    @54
    @38
    @0
    @50
    @60
    cr
    wcel
    @51
    @0
    @50
    wa
    @20
    cA
    @52
    @0
    @50
    simpl
    remulcld
    sylan2
    addge01d
    mpbid
    @0
    @33
    @68
    @61
    @45
    wceq
    @38
    @34
    @69
    @33
    @68
    wa
    #
    @61
    @21
    cA
    @60
    caddc
    co
    caddc
    co
    #
    @45
    @70
    @21
    cA
    @60
    @70
    @36
    @20
    cc
    wcel
    #
    @21
    cc
    wcel
    ax-1cn
    cA
    @19
    mulcl
    #
    c1
    @20
    addcl
    sylancr
    @33
    @68
    simpl
    #
    @70
    @20
    cA
    @73
    @74
    mulcld
    addassd
    @70
    @72
    @33
    @45
    @71
    wceq
    @73
    @74
    @20
    cA
    muladd11
    syl2anc
    eqtr4d
    syl2an
    breqtrd
    adantr
    @42
    @21
    @22
    @6
    @40
    @47
    @41
    @53
    adantr
    @40
    @58
    @41
    @59
    adantr
    @40
    @55
    @41
    @57
    adantr
    @0
    @3
    cc0
    @6
    cle
    wbr
    #
    @38
    @23
    @0
    @3
    @75
    @0
    @3
    c1
    @2
    caddc
    co
    #
    @6
    cle
    wbr
    #
    @75
    @2
    cr
    wcel
    @0
    @48
    @3
    @77
    wb
    neg1rr
    1re
    @2
    cA
    c1
    leadd2
    mp3an13
    @76
    cc0
    @6
    cle
    1pneg1e0
    breq1i
    syl6bb
    biimpa
    ad2ant2r
    @40
    @3
    @23
    simprr
    lemul1ad
    letrd
    @40
    @26
    @43
    wceq
    #
    @41
    @0
    @33
    @68
    @78
    @38
    @34
    @69
    @70
    @26
    c1
    @20
    cA
    caddc
    co
    #
    caddc
    co
    #
    @43
    @70
    @25
    @79
    c1
    caddc
    @70
    @25
    @20
    cA
    c1
    cmul
    co
    #
    caddc
    co
    #
    @79
    @33
    @68
    @36
    @25
    @82
    wceq
    ax-1cn
    cA
    @19
    c1
    adddi
    mp3an3
    @70
    @81
    cA
    @20
    caddc
    @33
    @81
    cA
    wceq
    @68
    cA
    mulid1
    adantr
    oveq2d
    eqtrd
    oveq2d
    @70
    @72
    @33
    @43
    @80
    wceq
    #
    @73
    @74
    @36
    @72
    @33
    @83
    ax-1cn
    c1
    @20
    cA
    addass
    mp3an1
    syl2anc
    eqtr4d
    syl2an
    adantr
    @40
    @27
    @44
    wceq
    #
    @41
    @0
    @35
    @38
    @84
    @0
    @36
    @33
    @35
    ax-1cn
    @34
    @37
    sylancr
    @6
    @19
    expp1
    sylan
    adantr
    3brtr4d
    exp43
    com12
    impd
    a2d
    nn0ind
    expd
    com12
    3imp
end
