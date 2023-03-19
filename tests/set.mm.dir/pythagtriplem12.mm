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
include "cmul.mm"
include "cc.mm"
include "nncn.mm"
include "addcl.mm"
include "syl2anr.mm"
include "3adant1.mm"
include "sqrtcld.mm"
include "subcl.mm"
include "addcld.mm"
include "3ad2ant1.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "sqdiv.mm"
include "mp3an23.mm"
include "sqvali.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "syl.mm"
include "binom2.mm"
include "syl2anc.mm"
include "cr.mm"
include "cle.mm"
include "nnre.mm"
include "readdcl.mm"
include "clt.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "nngt0.mm"
include "addgt0d.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "sylc.mm"
include "resqrtth.mm"
include "oveq1d.mm"
include "resubcl.mm"
include "pythagtriplem10.mm"
include "3adant3.mm"
include "oveq12d.mm"
include "mulcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "add32d.mm"
include "adddi.mm"
include "mp3an1.mm"
include "ppncand.mm"
include "2timesd.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "sqcld.mm"
include "pncand.mm"
include "subsq.mm"
include "3eqtr3rd.mm"
include "fveq2d.mm"
include "sqrtmuld.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "sqrtsqd.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "3adant2.mm"
include "2cnne0.mm"
include "divdiv1.mm"
include "divcan3.mm"
include "syl5eq.mm"

theorem pythagtriplem12
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  assume pythagtriplem11.1: |- M = ( ( ( sqrt ` ( C + B ) ) + ( sqrt ` ( C - B ) ) ) / 2 )


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> ( M ^ 2 ) = ( ( C + A ) / 2 ) )

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
    cM
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
    caddc
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
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cM
    @16
    c2
    cexp
    pythagtriplem11.1
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
    cmul
    co
    #
    cdiv
    co
    #
    c2
    @18
    cmul
    co
    #
    c2
    cdiv
    co
    #
    c2
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
    @3
    @8
    @26
    @9
    @3
    @12
    @14
    @3
    @11
    @1
    @2
    @11
    cc
    wcel
    #
    @0
    @2
    cC
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @27
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
    3adant1
    #
    sqrtcld
    #
    @3
    @13
    @1
    @2
    @13
    cc
    wcel
    #
    @0
    @2
    @28
    @29
    @34
    @1
    @30
    @31
    cC
    cB
    subcl
    syl2anr
    3adant1
    #
    sqrtcld
    #
    addcld
    3ad2ant1
    @26
    @17
    @20
    c2
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @22
    @26
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @17
    @38
    wceq
    2cn
    2ne0
    @15
    c2
    sqdiv
    mp3an23
    @37
    @21
    @20
    cdiv
    c2
    2cn
    sqvali
    oveq2i
    syl6eq
    syl
    @10
    @22
    @23
    @21
    cdiv
    co
    #
    @25
    @10
    @20
    @23
    @21
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
    caddc
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
    @11
    @44
    caddc
    co
    #
    @13
    caddc
    co
    #
    @23
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
    @47
    wceq
    @3
    @8
    @50
    @9
    @33
    3ad2ant1
    @3
    @8
    @51
    @9
    @36
    3ad2ant1
    @12
    @14
    binom2
    syl2anc
    @10
    @45
    @48
    @46
    @13
    caddc
    @10
    @42
    @11
    @44
    caddc
    @10
    @11
    cr
    wcel
    #
    cc0
    @11
    cle
    wbr
    #
    @42
    @11
    wceq
    @3
    @8
    @52
    @9
    @1
    @2
    @52
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
    @52
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
    3adant1
    3ad2ant1
    #
    @10
    @52
    cc0
    @11
    clt
    wbr
    #
    @53
    @58
    @3
    @8
    @59
    @9
    @3
    cC
    cB
    @2
    @0
    @54
    @1
    @56
    3ad2ant3
    @1
    @0
    @55
    @2
    @57
    3ad2ant2
    @2
    @0
    cc0
    cC
    clt
    wbr
    @1
    cC
    nngt0
    3ad2ant3
    @1
    @0
    cc0
    cB
    clt
    wbr
    @2
    cB
    nngt0
    3ad2ant2
    addgt0d
    3ad2ant1
    cc0
    cr
    wcel
    #
    @52
    @59
    @53
    wi
    0re
    cc0
    @11
    ltle
    mpan
    sylc
    #
    @11
    resqrtth
    syl2anc
    oveq1d
    @10
    @13
    cr
    wcel
    #
    cc0
    @13
    cle
    wbr
    #
    @46
    @13
    wceq
    @3
    @8
    @62
    @9
    @1
    @2
    @62
    @0
    @2
    @54
    @55
    @62
    @1
    @56
    @57
    cC
    cB
    resubcl
    syl2anr
    3adant1
    3ad2ant1
    #
    @10
    @62
    cc0
    @13
    clt
    wbr
    #
    @63
    @64
    @3
    @8
    @65
    @9
    cA
    cB
    cC
    pythagtriplem10
    3adant3
    @60
    @62
    @65
    @63
    wi
    0re
    cc0
    @13
    ltle
    mpan
    sylc
    #
    @13
    resqrtth
    syl2anc
    oveq12d
    @10
    @49
    @11
    @13
    caddc
    co
    #
    @44
    caddc
    co
    #
    @23
    @10
    @11
    @44
    @13
    @3
    @8
    @27
    @9
    @32
    3ad2ant1
    @3
    @8
    @44
    cc
    wcel
    #
    @9
    @3
    @39
    @43
    cc
    wcel
    @69
    2cn
    @3
    @12
    @14
    @33
    @36
    mulcld
    c2
    @43
    mulcl
    sylancr
    3ad2ant1
    @3
    @8
    @34
    @9
    @35
    3ad2ant1
    add32d
    @10
    @23
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
    caddc
    co
    #
    @68
    @10
    @28
    cA
    cc
    wcel
    #
    @23
    @72
    wceq
    #
    @3
    @8
    @28
    @9
    @2
    @0
    @28
    @1
    @30
    3ad2ant3
    3ad2ant1
    #
    @3
    @8
    @73
    @9
    @0
    @1
    @73
    @2
    cA
    nncn
    #
    3ad2ant1
    3ad2ant1
    #
    @39
    @28
    @73
    @74
    2cn
    c2
    cC
    cA
    adddi
    mp3an1
    syl2anc
    @10
    @67
    @70
    @44
    @71
    caddc
    @10
    @67
    cC
    cC
    caddc
    co
    @70
    @10
    cC
    cB
    cC
    @75
    @3
    @8
    @29
    @9
    @1
    @0
    @29
    @2
    @31
    3ad2ant2
    3ad2ant1
    #
    @75
    ppncand
    @10
    cC
    @75
    2timesd
    eqtr4d
    @10
    @43
    cA
    c2
    cmul
    @10
    @11
    @13
    cmul
    co
    #
    csqrt
    cfv
    @4
    csqrt
    cfv
    @43
    cA
    @10
    @79
    @4
    csqrt
    @10
    @6
    @5
    cmin
    co
    #
    @7
    @5
    cmin
    co
    #
    @4
    @79
    @8
    @3
    @80
    @81
    wceq
    @9
    @6
    @7
    @5
    cmin
    oveq1
    3ad2ant2
    @10
    @4
    @5
    @10
    cA
    @77
    sqcld
    @10
    cB
    @78
    sqcld
    pncand
    @10
    @28
    @29
    @81
    @79
    wceq
    @75
    @78
    cC
    cB
    subsq
    syl2anc
    3eqtr3rd
    fveq2d
    @10
    @11
    @13
    @58
    @61
    @64
    @66
    sqrtmuld
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
    @82
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
    @83
    @2
    @0
    cA
    cA
    nnnn0
    nn0ge0d
    3ad2ant1
    3ad2ant1
    sqrtsqd
    3eqtr3d
    oveq2d
    oveq12d
    eqtr4d
    eqtr4d
    3eqtrd
    oveq1d
    @10
    @23
    cc
    wcel
    #
    @25
    @41
    wceq
    #
    @10
    @39
    @18
    cc
    wcel
    #
    @84
    2cn
    @3
    @8
    @86
    @9
    @0
    @2
    @86
    @1
    @2
    @28
    @73
    @86
    @0
    @30
    @76
    cC
    cA
    addcl
    syl2anr
    3adant2
    3ad2ant1
    #
    c2
    @18
    mulcl
    sylancr
    @84
    @39
    @40
    wa
    #
    @88
    @85
    2cnne0
    2cnne0
    @23
    c2
    c2
    divdiv1
    mp3an23
    syl
    eqtr4d
    @10
    @24
    @18
    c2
    cdiv
    @10
    @86
    @24
    @18
    wceq
    #
    @87
    @86
    @39
    @40
    @89
    2cn
    2ne0
    @18
    c2
    divcan3
    mp3an23
    syl
    oveq1d
    3eqtrd
    syl5eq
end
