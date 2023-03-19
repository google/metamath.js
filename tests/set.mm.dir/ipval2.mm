include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "c1.mm"
include "c4.mm"
include "cfz.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cfv.mm"
include "c2.mm"
include "cmul.mm"
include "csu.mm"
include "cdiv.mm"
include "cneg.mm"
include "cmin.mm"
include "caddc.mm"
include "ipval.mm"
include "cc.mm"
include "ax-icn.mm"
include "ipval2lem4.mm"
include "mpan2.mm"
include "mulcl.mm"
include "sylancr.mm"
include "neg1cn.mm"
include "subcld.mm"
include "negicn.mm"
include "negsubd.mm"
include "mulm1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "wceq.mm"
include "mulneg1.mm"
include "oveq12d.mm"
include "subdi.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "sub32d.mm"
include "3eqtr4d.mm"
include "wa.mm"
include "nvsid.mm"
include "fveq2d.mm"
include "3adant2.mm"
include "ipval2lem3.mm"
include "recnd.mm"
include "mulid2d.mm"
include "cn.mm"
include "c3.mm"
include "nnuz.mm"
include "df-4.mm"
include "oveq2.mm"
include "i4.mm"
include "syl6eq.mm"
include "cn0.mm"
include "nnnn0.mm"
include "expcl.mm"
include "adantl.mm"
include "sylan2.mm"
include "mulcld.mm"
include "df-3.mm"
include "i3.mm"
include "df-2.mm"
include "i2.mm"
include "cz.mm"
include "1z.mm"
include "exp1.mm"
include "ax-mp.mm"
include "fsum1.mm"
include "1nn.mm"
include "jctil.mm"
include "eqidd.mm"
include "fsump1i.mm"
include "simprd.mm"
include "addcomd.mm"
include "subadd23d.mm"
include "eqtr4d.mm"

theorem ipval2
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume dipfval.1: |- X = ( BaseSet ` U )
  assume dipfval.2: |- G = ( +v ` U )
  assume dipfval.4: |- S = ( .sOLD ` U )
  assume dipfval.6: |- N = ( normCV ` U )
  assume dipfval.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A P B ) = ( ( ( ( ( N ` ( A G B ) ) ^ 2 ) - ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) + ( _i x. ( ( ( N ` ( A G ( _i S B ) ) ) ^ 2 ) - ( ( N ` ( A G ( -u _i S B ) ) ) ^ 2 ) ) ) ) / 4 ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cP
    co
    c1
    c4
    cfz
    co
    ci
    vk
    cv
    #
    cexp
    co
    #
    cA
    @5
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    c4
    cdiv
    co
    cA
    cB
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cA
    c1
    cneg
    #
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    ci
    cA
    ci
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cA
    ci
    cneg
    #
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
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
    caddc
    co
    #
    c4
    cdiv
    co
    cA
    cB
    cP
    cS
    cU
    vk
    cG
    cN
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    dipfval.6
    dipfval.7
    ipval
    @3
    @11
    @32
    c4
    cdiv
    @3
    ci
    @24
    cmul
    co
    #
    @15
    @19
    cmul
    co
    #
    caddc
    co
    #
    @25
    @29
    cmul
    co
    #
    caddc
    co
    #
    c1
    cA
    c1
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @31
    @19
    cmin
    co
    #
    @14
    caddc
    co
    #
    @11
    @32
    @3
    @37
    @44
    @42
    @14
    caddc
    @3
    @33
    @19
    cmin
    co
    #
    ci
    @29
    cmul
    co
    #
    cneg
    #
    caddc
    co
    @46
    @47
    cmin
    co
    #
    @37
    @44
    @3
    @46
    @47
    @3
    @33
    @19
    @3
    ci
    cc
    wcel
    #
    @24
    cc
    wcel
    #
    @33
    cc
    wcel
    #
    ax-icn
    @3
    @50
    @51
    ax-icn
    cA
    cB
    ci
    cP
    cS
    cU
    cG
    cN
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    dipfval.6
    dipfval.7
    ipval2lem4
    mpan2
    #
    ci
    @24
    mulcl
    sylancr
    #
    @3
    @15
    cc
    wcel
    @19
    cc
    wcel
    neg1cn
    cA
    cB
    @15
    cP
    cS
    cU
    cG
    cN
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    dipfval.6
    dipfval.7
    ipval2lem4
    mpan2
    #
    subcld
    @3
    @50
    @29
    cc
    wcel
    #
    @47
    cc
    wcel
    ax-icn
    @3
    @25
    cc
    wcel
    @56
    negicn
    cA
    cB
    @25
    cP
    cS
    cU
    cG
    cN
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    dipfval.6
    dipfval.7
    ipval2lem4
    mpan2
    #
    ci
    @29
    mulcl
    sylancr
    #
    negsubd
    @3
    @35
    @46
    @36
    @48
    caddc
    @3
    @35
    @33
    @19
    cneg
    #
    caddc
    co
    @46
    @3
    @34
    @59
    @33
    caddc
    @3
    @19
    @55
    mulm1d
    oveq2d
    @3
    @33
    @19
    @54
    @55
    negsubd
    eqtrd
    @3
    @50
    @56
    @36
    @48
    wceq
    ax-icn
    @57
    ci
    @29
    mulneg1
    sylancr
    oveq12d
    @3
    @44
    @33
    @47
    cmin
    co
    #
    @19
    cmin
    co
    @49
    @3
    @31
    @60
    @19
    cmin
    @3
    @51
    @56
    @31
    @60
    wceq
    #
    @53
    @57
    @50
    @51
    @56
    @61
    ax-icn
    ci
    @24
    @29
    subdi
    mp3an1
    syl2anc
    oveq1d
    @3
    @33
    @47
    @19
    @54
    @58
    @55
    sub32d
    eqtrd
    3eqtr4d
    @3
    @42
    c1
    @14
    cmul
    co
    @14
    @3
    @41
    @14
    c1
    cmul
    @0
    @2
    @41
    @14
    wceq
    @1
    @0
    @2
    wa
    #
    @40
    @13
    c2
    cexp
    @62
    @39
    @12
    cN
    @62
    @38
    cB
    cA
    cG
    cB
    cS
    cU
    cX
    dipfval.1
    dipfval.4
    nvsid
    oveq2d
    fveq2d
    oveq1d
    3adant2
    oveq2d
    @3
    @14
    @3
    @14
    cA
    cB
    cP
    cS
    cU
    cG
    cN
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    dipfval.6
    dipfval.7
    ipval2lem3
    recnd
    #
    mulid2d
    eqtrd
    oveq12d
    @3
    c4
    cn
    wcel
    @11
    @43
    wceq
    @3
    @10
    @42
    @37
    @43
    vk
    c3
    c1
    c4
    cn
    nnuz
    df-4
    @4
    c4
    wceq
    #
    @5
    c1
    @9
    @41
    cmul
    @64
    @5
    ci
    c4
    cexp
    co
    c1
    @4
    c4
    ci
    cexp
    oveq2
    i4
    syl6eq
    #
    @64
    @8
    @40
    c2
    cexp
    @64
    @7
    @39
    cN
    @64
    @6
    @38
    cA
    cG
    @64
    @5
    c1
    cB
    cS
    @65
    oveq1d
    oveq2d
    fveq2d
    oveq1d
    oveq12d
    @3
    @4
    cn
    wcel
    #
    wa
    @5
    @9
    @66
    @5
    cc
    wcel
    #
    @3
    @66
    @50
    @4
    cn0
    wcel
    @67
    ax-icn
    @4
    nnnn0
    ci
    @4
    expcl
    sylancr
    #
    adantl
    @66
    @3
    @67
    @9
    cc
    wcel
    @68
    cA
    cB
    @5
    cP
    cS
    cU
    cG
    cN
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    dipfval.6
    dipfval.7
    ipval2lem4
    sylan2
    mulcld
    #
    @3
    @10
    @36
    @35
    @37
    vk
    c2
    c1
    c3
    cn
    nnuz
    df-3
    @4
    c3
    wceq
    #
    @5
    @25
    @9
    @29
    cmul
    @70
    @5
    ci
    c3
    cexp
    co
    @25
    @4
    c3
    ci
    cexp
    oveq2
    i3
    syl6eq
    #
    @70
    @8
    @28
    c2
    cexp
    @70
    @7
    @27
    cN
    @70
    @6
    @26
    cA
    cG
    @70
    @5
    @25
    cB
    cS
    @71
    oveq1d
    oveq2d
    fveq2d
    oveq1d
    oveq12d
    @69
    @3
    @10
    @34
    @33
    @35
    vk
    c1
    c1
    c2
    cn
    nnuz
    df-2
    @4
    c2
    wceq
    #
    @5
    @15
    @9
    @19
    cmul
    @72
    @5
    ci
    c2
    cexp
    co
    @15
    @4
    c2
    ci
    cexp
    oveq2
    i2
    syl6eq
    #
    @72
    @8
    @18
    c2
    cexp
    @72
    @7
    @17
    cN
    @72
    @6
    @16
    cA
    cG
    @72
    @5
    @15
    cB
    cS
    @73
    oveq1d
    oveq2d
    fveq2d
    oveq1d
    oveq12d
    @69
    @3
    c1
    c1
    cfz
    co
    @10
    vk
    csu
    @33
    wceq
    #
    c1
    cn
    wcel
    @3
    c1
    cz
    wcel
    @52
    @74
    1z
    @54
    @10
    @33
    vk
    c1
    @4
    c1
    wceq
    #
    @5
    ci
    @9
    @24
    cmul
    @75
    @5
    ci
    c1
    cexp
    co
    #
    ci
    @4
    c1
    ci
    cexp
    oveq2
    @50
    @76
    ci
    wceq
    ax-icn
    ci
    exp1
    ax-mp
    syl6eq
    #
    @75
    @8
    @23
    c2
    cexp
    @75
    @7
    @22
    cN
    @75
    @6
    @21
    cA
    cG
    @75
    @5
    ci
    cB
    cS
    @77
    oveq1d
    oveq2d
    fveq2d
    oveq1d
    oveq12d
    fsum1
    sylancr
    1nn
    jctil
    @3
    @35
    eqidd
    fsump1i
    @3
    @37
    eqidd
    fsump1i
    @3
    @43
    eqidd
    fsump1i
    simprd
    @3
    @32
    @31
    @20
    caddc
    co
    @45
    @3
    @20
    @31
    @3
    @14
    @19
    @63
    @55
    subcld
    @3
    @50
    @30
    cc
    wcel
    @31
    cc
    wcel
    ax-icn
    @3
    @24
    @29
    @53
    @57
    subcld
    ci
    @30
    mulcl
    sylancr
    #
    addcomd
    @3
    @31
    @19
    @14
    @78
    @55
    @63
    subadd23d
    eqtr4d
    3eqtr4d
    oveq1d
    eqtrd
end
