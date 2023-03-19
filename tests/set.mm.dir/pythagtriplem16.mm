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
include "cmul.mm"
include "cdiv.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmin.mm"
include "oveq12i.mm"
include "cc.mm"
include "nncn.mm"
include "addcl.mm"
include "syl2anr.mm"
include "sqrtcld.mm"
include "subcl.mm"
include "syl2anc.mm"
include "3adant1.mm"
include "3ad2ant1.mm"
include "cc0.mm"
include "wne.mm"
include "2cnne0.mm"
include "divmuldiv.mm"
include "mpanr12.mm"
include "mulcld.mm"
include "divdiv1.mm"
include "mp3an23.mm"
include "syl.mm"
include "eqtr4d.mm"
include "cr.mm"
include "cle.mm"
include "nnre.mm"
include "readdcl.mm"
include "clt.mm"
include "adantl.mm"
include "adantr.mm"
include "nngt0.mm"
include "addgt0d.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "sylc.mm"
include "resqrtth.mm"
include "resubcl.mm"
include "pythagtriplem10.mm"
include "3adant3.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "simp12.mm"
include "simp13.mm"
include "subsq.mm"
include "pnncan.mm"
include "3anidm23.mm"
include "2times.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan3.mm"
include "3syl.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "divcan2.mm"
include "3ad2ant2.mm"
include "eqtr2d.mm"

theorem pythagtriplem16
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cN: class N
  assume pythagtriplem15.1: |- M = ( ( ( sqrt ` ( C + B ) ) + ( sqrt ` ( C - B ) ) ) / 2 )
  assume pythagtriplem15.2: |- N = ( ( ( sqrt ` ( C + B ) ) - ( sqrt ` ( C - B ) ) ) / 2 )


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> B = ( 2 x. ( M x. N ) ) )

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
    cB
    c2
    cexp
    co
    caddc
    co
    cC
    c2
    cexp
    co
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
    c2
    cM
    cN
    cmul
    co
    #
    cmul
    co
    c2
    cB
    c2
    cdiv
    co
    #
    cmul
    co
    #
    cB
    @6
    @7
    @8
    c2
    cmul
    @6
    @7
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
    @11
    @13
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @8
    cM
    @15
    cN
    @17
    cmul
    pythagtriplem15.1
    pythagtriplem15.2
    oveq12i
    @6
    @18
    @14
    @16
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
    @8
    @6
    @18
    @19
    c2
    c2
    cmul
    co
    cdiv
    co
    #
    @21
    @6
    @14
    cc
    wcel
    #
    @16
    cc
    wcel
    #
    @18
    @22
    wceq
    #
    @3
    @4
    @23
    @5
    @1
    @2
    @23
    @0
    @1
    @2
    wa
    #
    @11
    cc
    wcel
    #
    @13
    cc
    wcel
    #
    @23
    @26
    @10
    @2
    cC
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @10
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
    @26
    @12
    @2
    @29
    @30
    @12
    cc
    wcel
    @1
    @31
    @32
    cC
    cB
    subcl
    syl2anr
    sqrtcld
    #
    @11
    @13
    addcl
    syl2anc
    #
    3adant1
    3ad2ant1
    @3
    @4
    @24
    @5
    @1
    @2
    @24
    @0
    @26
    @27
    @28
    @24
    @33
    @34
    @11
    @13
    subcl
    syl2anc
    #
    3adant1
    3ad2ant1
    @23
    @24
    wa
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    wa
    #
    @39
    @25
    2cnne0
    2cnne0
    @14
    @16
    c2
    c2
    divmuldiv
    mpanr12
    syl2anc
    @6
    @19
    cc
    wcel
    #
    @21
    @22
    wceq
    #
    @3
    @4
    @40
    @5
    @1
    @2
    @40
    @0
    @26
    @14
    @16
    @35
    @36
    mulcld
    3adant1
    3ad2ant1
    @40
    @39
    @39
    @41
    2cnne0
    2cnne0
    @19
    c2
    c2
    divdiv1
    mp3an23
    syl
    eqtr4d
    @6
    @20
    cB
    c2
    cdiv
    @6
    @11
    c2
    cexp
    co
    #
    @13
    c2
    cexp
    co
    #
    cmin
    co
    #
    c2
    cdiv
    co
    @10
    @12
    cmin
    co
    #
    c2
    cdiv
    co
    #
    @20
    cB
    @6
    @44
    @45
    c2
    cdiv
    @6
    @42
    @10
    @43
    @12
    cmin
    @6
    @10
    cr
    wcel
    #
    cc0
    @10
    cle
    wbr
    #
    @42
    @10
    wceq
    @3
    @4
    @47
    @5
    @1
    @2
    @47
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
    @47
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
    @3
    @4
    @48
    @5
    @1
    @2
    @48
    @0
    @26
    @47
    cc0
    @10
    clt
    wbr
    #
    @48
    @53
    @26
    cC
    cB
    @2
    @49
    @1
    @51
    adantl
    @1
    @50
    @2
    @52
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
    @47
    @54
    @48
    wi
    0re
    cc0
    @10
    ltle
    mpan
    sylc
    3adant1
    3ad2ant1
    @10
    resqrtth
    syl2anc
    @6
    @12
    cr
    wcel
    #
    cc0
    @12
    cle
    wbr
    #
    @43
    @12
    wceq
    @3
    @4
    @56
    @5
    @1
    @2
    @56
    @0
    @2
    @49
    @50
    @56
    @1
    @51
    @52
    cC
    cB
    resubcl
    syl2anr
    3adant1
    3ad2ant1
    #
    @6
    @56
    cc0
    @12
    clt
    wbr
    #
    @57
    @58
    @3
    @4
    @59
    @5
    cA
    cB
    cC
    pythagtriplem10
    3adant3
    @55
    @56
    @59
    @57
    wi
    0re
    cc0
    @12
    ltle
    mpan
    sylc
    @12
    resqrtth
    syl2anc
    oveq12d
    oveq1d
    @6
    @44
    @19
    c2
    cdiv
    @6
    @27
    @28
    @44
    @19
    wceq
    @6
    @1
    @2
    @27
    @0
    @1
    @2
    @4
    @5
    simp12
    #
    @0
    @1
    @2
    @4
    @5
    simp13
    #
    @33
    syl2anc
    @6
    @1
    @2
    @28
    @60
    @61
    @34
    syl2anc
    @11
    @13
    subsq
    syl2anc
    oveq1d
    @6
    @46
    c2
    cB
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cB
    @6
    @45
    @62
    c2
    cdiv
    @3
    @4
    @45
    @62
    wceq
    #
    @5
    @1
    @2
    @64
    @0
    @2
    @29
    @30
    @64
    @1
    @31
    @32
    @29
    @30
    wa
    @45
    cB
    cB
    caddc
    co
    #
    @62
    @29
    @30
    @45
    @65
    wceq
    cC
    cB
    cB
    pnncan
    3anidm23
    @30
    @62
    @65
    wceq
    @29
    cB
    2times
    adantl
    eqtr4d
    syl2anr
    3adant1
    3ad2ant1
    oveq1d
    @6
    @1
    @30
    @63
    cB
    wceq
    #
    @60
    @32
    @30
    @37
    @38
    @66
    2cn
    2ne0
    cB
    c2
    divcan3
    mp3an23
    3syl
    eqtrd
    3eqtr3d
    oveq1d
    eqtrd
    syl5eq
    oveq2d
    @3
    @4
    @9
    cB
    wceq
    #
    @5
    @1
    @0
    @67
    @2
    @1
    @30
    @67
    @32
    @30
    @37
    @38
    @67
    2cn
    2ne0
    cB
    c2
    divcan2
    mp3an23
    syl
    3ad2ant2
    3ad2ant1
    eqtr2d
end
