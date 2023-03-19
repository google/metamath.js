include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cgcd.mm"
include "c1.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "oveq1i.mm"
include "cc.mm"
include "nncn.mm"
include "addcl.mm"
include "syl2anr.mm"
include "sqrtcld.mm"
include "subcl.mm"
include "subcld.mm"
include "3adant1.mm"
include "3ad2ant1.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "sqdiv.mm"
include "mp3an23.mm"
include "syl.mm"
include "cmul.mm"
include "sqvali.mm"
include "oveq2i.mm"
include "sqcld.mm"
include "2cnne0.mm"
include "divdiv1.mm"
include "simp12.mm"
include "simp13.mm"
include "syl2anc.mm"
include "binom2sub.mm"
include "cr.mm"
include "nnre.mm"
include "readdcl.mm"
include "recnd.mm"
include "resubcl.mm"
include "mulcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addsubd.mm"
include "nncnd.mm"
include "simp11.mm"
include "subdi.mm"
include "mp3an1.mm"
include "ppncan.mm"
include "3anidm13.mm"
include "2times.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "subsq.mm"
include "oveq1.mm"
include "3ad2ant2.mm"
include "pncand.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "cle.mm"
include "clt.mm"
include "adantl.mm"
include "nngt0.mm"
include "addgt0d.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "sylc.mm"
include "pythagtriplem10.mm"
include "3adant3.mm"
include "sqrtmuld.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "sqrtsqd.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "resqrtth.mm"
include "oveq1d.mm"
include "3eqtr4rd.mm"
include "eqtrd.mm"
include "3adant2.mm"
include "divcan3.mm"
include "syl5eq.mm"

theorem pythagtriplem14
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  assume pythagtriplem13.1: |- N = ( ( ( sqrt ` ( C + B ) ) - ( sqrt ` ( C - B ) ) ) / 2 )


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> ( N ^ 2 ) = ( ( C - A ) / 2 ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    cC
    c2
    cexp
    co
    #
    wceq
    #
    cA
    cB
    cgcd
    co
    c1
    wceq
    c2
    cA
    cdvds
    wbr
    wn
    wa
    #
    w3a
    #
    cN
    c2
    cexp
    co
    cC
    cB
    caddc
    co
    #
    csqrt
    cfv
    #
    cC
    cB
    cmin
    co
    #
    csqrt
    cfv
    #
    cmin
    co
    #
    c2
    cdiv
    co
    #
    c2
    cexp
    co
    #
    cC
    cA
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cN
    @16
    c2
    cexp
    pythagtriplem13.1
    oveq1i
    @10
    @17
    @15
    c2
    cexp
    co
    #
    c2
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @19
    @10
    @15
    cc
    wcel
    #
    @17
    @22
    wceq
    #
    @3
    @8
    @23
    @9
    @1
    @2
    @23
    @0
    @1
    @2
    wa
    #
    @12
    @14
    @25
    @11
    @2
    cC
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @11
    cc
    wcel
    @1
    cC
    nncn
    #
    cB
    nncn
    #
    cC
    cB
    addcl
    syl2anr
    sqrtcld
    #
    @25
    @13
    @2
    @26
    @27
    @13
    cc
    wcel
    @1
    @28
    @29
    cC
    cB
    subcl
    syl2anr
    sqrtcld
    #
    subcld
    3adant1
    3ad2ant1
    #
    @23
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @24
    2cn
    2ne0
    @15
    c2
    sqdiv
    mp3an23
    syl
    @10
    @22
    @20
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    #
    @19
    @21
    @35
    @20
    cdiv
    c2
    2cn
    sqvali
    oveq2i
    @10
    @20
    c2
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    @36
    @19
    @10
    @20
    cc
    wcel
    #
    @38
    @36
    wceq
    #
    @10
    @15
    @32
    sqcld
    @39
    @33
    @34
    wa
    #
    @41
    @40
    2cnne0
    2cnne0
    @20
    c2
    c2
    divdiv1
    mp3an23
    syl
    @10
    @37
    @18
    c2
    cdiv
    @10
    @37
    c2
    @18
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @18
    @10
    @20
    @42
    c2
    cdiv
    @10
    @20
    @12
    c2
    cexp
    co
    #
    c2
    @12
    @14
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @14
    c2
    cexp
    co
    #
    caddc
    co
    #
    @42
    @10
    @12
    cc
    wcel
    #
    @14
    cc
    wcel
    #
    @20
    @49
    wceq
    @10
    @1
    @2
    @50
    @0
    @1
    @2
    @8
    @9
    simp12
    #
    @0
    @1
    @2
    @8
    @9
    simp13
    #
    @30
    syl2anc
    @10
    @1
    @2
    @51
    @52
    @53
    @31
    syl2anc
    @12
    @14
    binom2sub
    syl2anc
    @10
    @11
    @13
    caddc
    co
    #
    @46
    cmin
    co
    #
    @11
    @46
    cmin
    co
    #
    @13
    caddc
    co
    @42
    @49
    @10
    @11
    @13
    @46
    @10
    @11
    @3
    @8
    @11
    cr
    wcel
    #
    @9
    @1
    @2
    @57
    @0
    @2
    cC
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @57
    @1
    cC
    nnre
    #
    cB
    nnre
    #
    cC
    cB
    readdcl
    syl2anr
    #
    3adant1
    3ad2ant1
    #
    recnd
    @10
    @13
    @3
    @8
    @13
    cr
    wcel
    #
    @9
    @1
    @2
    @64
    @0
    @2
    @58
    @59
    @64
    @1
    @60
    @61
    cC
    cB
    resubcl
    syl2anr
    3adant1
    3ad2ant1
    #
    recnd
    @3
    @8
    @46
    cc
    wcel
    #
    @9
    @3
    @33
    @45
    cc
    wcel
    @66
    2cn
    @3
    @12
    @14
    @1
    @2
    @50
    @0
    @30
    3adant1
    @1
    @2
    @51
    @0
    @31
    3adant1
    mulcld
    c2
    @45
    mulcl
    sylancr
    3ad2ant1
    addsubd
    @10
    @42
    c2
    cC
    cmul
    co
    #
    c2
    cA
    cmul
    co
    #
    cmin
    co
    #
    @55
    @10
    @26
    cA
    cc
    wcel
    #
    @42
    @69
    wceq
    #
    @10
    cC
    @53
    nncnd
    #
    @10
    cA
    @0
    @1
    @2
    @8
    @9
    simp11
    nncnd
    @33
    @26
    @70
    @71
    2cn
    c2
    cC
    cA
    subdi
    mp3an1
    syl2anc
    @10
    @54
    @67
    @46
    @68
    cmin
    @3
    @8
    @54
    @67
    wceq
    #
    @9
    @1
    @2
    @73
    @0
    @2
    @26
    @27
    @73
    @1
    @28
    @29
    @26
    @27
    wa
    @54
    cC
    cC
    caddc
    co
    #
    @67
    @26
    @27
    @54
    @74
    wceq
    cC
    cB
    cC
    ppncan
    3anidm13
    @26
    @67
    @74
    wceq
    @27
    cC
    2times
    adantr
    eqtr4d
    syl2anr
    3adant1
    3ad2ant1
    @10
    @45
    cA
    c2
    cmul
    @10
    @4
    csqrt
    cfv
    #
    @45
    cA
    @10
    @11
    @13
    cmul
    co
    #
    csqrt
    cfv
    @75
    @45
    @10
    @76
    @4
    csqrt
    @10
    @7
    @5
    cmin
    co
    #
    @76
    @4
    @10
    @26
    @27
    @77
    @76
    wceq
    @72
    @10
    cB
    @52
    nncnd
    cC
    cB
    subsq
    syl2anc
    @10
    @6
    @5
    cmin
    co
    #
    @77
    @4
    @8
    @3
    @78
    @77
    wceq
    @9
    @6
    @7
    @5
    cmin
    oveq1
    3ad2ant2
    @3
    @8
    @78
    @4
    wceq
    @9
    @3
    @4
    @5
    @0
    @1
    @4
    cc
    wcel
    @2
    @0
    cA
    cA
    nncn
    #
    sqcld
    3ad2ant1
    @1
    @0
    @5
    cc
    wcel
    @2
    @1
    cB
    @29
    sqcld
    3ad2ant2
    pncand
    3ad2ant1
    eqtr3d
    eqtr3d
    fveq2d
    @10
    @11
    @13
    @63
    @3
    @8
    cc0
    @11
    cle
    wbr
    #
    @9
    @1
    @2
    @80
    @0
    @25
    @57
    cc0
    @11
    clt
    wbr
    #
    @80
    @62
    @25
    cC
    cB
    @2
    @58
    @1
    @60
    adantl
    @1
    @59
    @2
    @61
    adantr
    @2
    cc0
    cC
    clt
    wbr
    @1
    cC
    nngt0
    adantl
    @1
    cc0
    cB
    clt
    wbr
    @2
    cB
    nngt0
    adantr
    addgt0d
    cc0
    cr
    wcel
    #
    @57
    @81
    @80
    wi
    0re
    cc0
    @11
    ltle
    mpan
    sylc
    3adant1
    3ad2ant1
    #
    @65
    @10
    @64
    cc0
    @13
    clt
    wbr
    #
    cc0
    @13
    cle
    wbr
    #
    @65
    @3
    @8
    @84
    @9
    cA
    cB
    cC
    pythagtriplem10
    3adant3
    @82
    @64
    @84
    @85
    wi
    0re
    cc0
    @13
    ltle
    mpan
    sylc
    #
    sqrtmuld
    eqtr3d
    @10
    cA
    @3
    @8
    cA
    cr
    wcel
    #
    @9
    @0
    @1
    @87
    @2
    cA
    nnre
    3ad2ant1
    3ad2ant1
    @3
    @8
    cc0
    cA
    cle
    wbr
    #
    @9
    @0
    @1
    @88
    @2
    @0
    cA
    cA
    nnnn0
    nn0ge0d
    3ad2ant1
    3ad2ant1
    sqrtsqd
    eqtr3d
    oveq2d
    oveq12d
    eqtr4d
    @10
    @47
    @56
    @48
    @13
    caddc
    @10
    @44
    @11
    @46
    cmin
    @10
    @57
    @80
    @44
    @11
    wceq
    @63
    @83
    @11
    resqrtth
    syl2anc
    oveq1d
    @10
    @64
    @85
    @48
    @13
    wceq
    @65
    @86
    @13
    resqrtth
    syl2anc
    oveq12d
    3eqtr4rd
    eqtrd
    oveq1d
    @10
    @18
    cc
    wcel
    #
    @43
    @18
    wceq
    #
    @3
    @8
    @89
    @9
    @0
    @2
    @89
    @1
    @2
    @26
    @70
    @89
    @0
    @28
    @79
    cC
    cA
    subcl
    syl2anr
    3adant2
    3ad2ant1
    @89
    @33
    @34
    @90
    2cn
    2ne0
    @18
    c2
    divcan3
    mp3an23
    syl
    eqtrd
    oveq1d
    eqtr3d
    syl5eq
    eqtrd
    syl5eq
end
