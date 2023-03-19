include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "wceq.mm"
include "caddc.mm"
include "w3a.mm"
include "cn.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "cc.mm"
include "nncn.mm"
include "sqcl.mm"
include "adantl.mm"
include "sqcld.mm"
include "2cn.mm"
include "mulcl.mm"
include "syl2anr.mm"
include "sylancr.mm"
include "subcld.mm"
include "adantr.mm"
include "ancoms.mm"
include "add32d.mm"
include "subadd23d.mm"
include "c4.mm"
include "sqmul.mm"
include "sq2.mm"
include "a1i.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "4cn.mm"
include "2p2e4.mm"
include "subaddrii.mm"
include "oveq1i.mm"
include "subdir.mm"
include "mp3an12.mm"
include "syl.mm"
include "syl5reqr.mm"
include "oveq2d.mm"
include "binom2sub.mm"
include "binom2.mm"
include "3eqtr4d.mm"
include "3adant3.mm"
include "simp3.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "sqmuld.mm"
include "3ad2ant3.mm"
include "adddid.mm"
include "eqtr4d.mm"
include "addcld.mm"
include "syl3an.mm"
include "oveq1.mm"
include "oveqan12d.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "3expa.mm"
include "rexlimdva.mm"
include "rexlimivv.mm"

theorem pythagtriplem1
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n

  disjoint A n
  disjoint A m
  disjoint A k
  disjoint m n
  disjoint k n
  disjoint k m
  disjoint B n
  disjoint B m
  disjoint B k
  disjoint C n
  disjoint C m
  disjoint C k
  assert |- ( E. n e. NN E. m e. NN E. k e. NN ( A = ( k x. ( ( m ^ 2 ) - ( n ^ 2 ) ) ) /\ B = ( k x. ( 2 x. ( m x. n ) ) ) /\ C = ( k x. ( ( m ^ 2 ) + ( n ^ 2 ) ) ) ) -> ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) )

  proof
    cA
    vk
    cv
    #
    vm
    cv
    #
    c2
    cexp
    co
    #
    vn
    cv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    wceq
    #
    cB
    @0
    c2
    @1
    @3
    cmul
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    wceq
    #
    cC
    @0
    @2
    @4
    caddc
    co
    #
    cmul
    co
    #
    wceq
    #
    w3a
    #
    vk
    cn
    wrex
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
    vn
    vm
    cn
    cn
    @3
    cn
    wcel
    #
    @1
    cn
    wcel
    #
    wa
    @15
    @20
    vk
    cn
    @21
    @22
    @0
    cn
    wcel
    #
    @15
    @20
    wi
    @21
    @22
    @23
    w3a
    @20
    @15
    @6
    c2
    cexp
    co
    #
    @10
    c2
    cexp
    co
    #
    caddc
    co
    #
    @13
    c2
    cexp
    co
    #
    wceq
    #
    @21
    @3
    cc
    wcel
    #
    @22
    @1
    cc
    wcel
    #
    @23
    @0
    cc
    wcel
    #
    @28
    @3
    nncn
    @1
    nncn
    @0
    nncn
    @29
    @30
    @31
    w3a
    #
    @0
    c2
    cexp
    co
    #
    @5
    c2
    cexp
    co
    #
    @9
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    @33
    @12
    c2
    cexp
    co
    #
    cmul
    co
    @26
    @27
    @32
    @36
    @38
    @33
    cmul
    @29
    @30
    @36
    @38
    wceq
    @31
    @29
    @30
    wa
    #
    @2
    c2
    cexp
    co
    #
    c2
    @2
    @4
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @4
    c2
    cexp
    co
    #
    caddc
    co
    #
    @35
    caddc
    co
    #
    @40
    @42
    caddc
    co
    #
    @44
    caddc
    co
    #
    @36
    @38
    @39
    @46
    @43
    @35
    caddc
    co
    #
    @44
    caddc
    co
    @48
    @39
    @43
    @44
    @35
    @39
    @40
    @42
    @39
    @2
    @30
    @2
    cc
    wcel
    #
    @29
    @1
    sqcl
    #
    adantl
    sqcld
    #
    @39
    c2
    cc
    wcel
    #
    @41
    cc
    wcel
    #
    @42
    cc
    wcel
    2cn
    @30
    @50
    @4
    cc
    wcel
    #
    @54
    @29
    @51
    @3
    sqcl
    #
    @2
    @4
    mulcl
    syl2anr
    #
    c2
    @41
    mulcl
    sylancr
    #
    subcld
    @39
    @4
    @29
    @55
    @30
    @56
    adantr
    sqcld
    @39
    @9
    @39
    @53
    @8
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    2cn
    @30
    @29
    @59
    @1
    @3
    mulcl
    ancoms
    #
    c2
    @8
    mulcl
    #
    sylancr
    sqcld
    #
    add32d
    @39
    @49
    @47
    @44
    caddc
    @39
    @49
    @40
    @35
    @42
    cmin
    co
    #
    caddc
    co
    @47
    @39
    @40
    @42
    @35
    @52
    @58
    @63
    subadd23d
    @39
    @64
    @42
    @40
    caddc
    @39
    @64
    c4
    @41
    cmul
    co
    #
    @42
    cmin
    co
    #
    @42
    @39
    @35
    @65
    @42
    cmin
    @39
    @35
    c2
    c2
    cexp
    co
    #
    @8
    c2
    cexp
    co
    #
    cmul
    co
    #
    @65
    @39
    @53
    @59
    @35
    @69
    wceq
    2cn
    @61
    c2
    @8
    sqmul
    sylancr
    @39
    @67
    c4
    @68
    @41
    cmul
    @67
    c4
    wceq
    @39
    sq2
    a1i
    @30
    @29
    @68
    @41
    wceq
    @1
    @3
    sqmul
    ancoms
    oveq12d
    eqtrd
    oveq1d
    @39
    @42
    c4
    c2
    cmin
    co
    #
    @41
    cmul
    co
    #
    @66
    @70
    c2
    @41
    cmul
    c4
    c2
    c2
    4cn
    2cn
    2cn
    2p2e4
    subaddrii
    oveq1i
    @39
    @54
    @71
    @66
    wceq
    #
    @57
    c4
    cc
    wcel
    @53
    @54
    @72
    4cn
    2cn
    c4
    c2
    @41
    subdir
    mp3an12
    syl
    syl5reqr
    eqtrd
    oveq2d
    eqtrd
    oveq1d
    eqtrd
    @39
    @34
    @45
    @35
    caddc
    @30
    @50
    @55
    @34
    @45
    wceq
    @29
    @51
    @56
    @2
    @4
    binom2sub
    syl2anr
    oveq1d
    @30
    @50
    @55
    @38
    @48
    wceq
    @29
    @51
    @56
    @2
    @4
    binom2
    syl2anr
    3eqtr4d
    3adant3
    oveq2d
    @32
    @26
    @33
    @34
    cmul
    co
    #
    @33
    @35
    cmul
    co
    #
    caddc
    co
    @37
    @32
    @24
    @73
    @25
    @74
    caddc
    @32
    @0
    @5
    @29
    @30
    @31
    simp3
    #
    @32
    @2
    @4
    @30
    @29
    @50
    @31
    @51
    3ad2ant2
    #
    @29
    @30
    @55
    @31
    @56
    3ad2ant1
    #
    subcld
    #
    sqmuld
    @32
    @0
    @9
    @75
    @32
    @53
    @59
    @60
    2cn
    @29
    @30
    @59
    @31
    @61
    3adant3
    @62
    sylancr
    #
    sqmuld
    oveq12d
    @32
    @33
    @34
    @35
    @31
    @29
    @33
    cc
    wcel
    @30
    @0
    sqcl
    3ad2ant3
    @32
    @5
    @78
    sqcld
    @32
    @9
    @79
    sqcld
    adddid
    eqtr4d
    @32
    @0
    @12
    @75
    @32
    @2
    @4
    @76
    @77
    addcld
    sqmuld
    3eqtr4d
    syl3an
    @15
    @18
    @26
    @19
    @27
    @7
    @11
    @18
    @26
    wceq
    @14
    @7
    @11
    @16
    @24
    @17
    @25
    caddc
    cA
    @6
    c2
    cexp
    oveq1
    cB
    @10
    c2
    cexp
    oveq1
    oveqan12d
    3adant3
    @14
    @7
    @19
    @27
    wceq
    @11
    cC
    @13
    c2
    cexp
    oveq1
    3ad2ant3
    eqeq12d
    syl5ibrcom
    3expa
    rexlimdva
    rexlimivv
end
