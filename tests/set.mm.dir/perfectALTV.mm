include "cn.mm"
include "wcel.mm"
include "ceven.mm"
include "wa.mm"
include "c1.mm"
include "csgm.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "wceq.mm"
include "cv.mm"
include "cexp.mm"
include "cmin.mm"
include "cprime.mm"
include "cz.mm"
include "wrex.mm"
include "cpc.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "2dvdseven.mm"
include "ad2antlr.mm"
include "wb.mm"
include "2prm.mm"
include "simpll.mm"
include "pcelnn.mm"
include "sylancr.mm"
include "mpbird.mm"
include "nnzd.mm"
include "peano2zd.mm"
include "cdiv.mm"
include "pcdvds.mm"
include "cn0.mm"
include "2nn.mm"
include "nnnn0d.mm"
include "nnexpcl.mm"
include "nndivdvds.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wn.mm"
include "codd.mm"
include "pcndvds2.mm"
include "isodd3.mm"
include "sylanbrc.mm"
include "simpr.mm"
include "cc.mm"
include "nncn.mm"
include "ad2antrr.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "perfectALTVlem2.mm"
include "simprd.mm"
include "simpld.mm"
include "eqeltrrd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "eqtr3d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ex.mm"
include "perfect1.mm"
include "2cn.mm"
include "mersenne.mm"
include "prmnn.mm"
include "syl.mm"
include "expm1t.mm"
include "nnm1nn0.mm"
include "expcl.mm"
include "mulcom.mm"
include "eqtrd.mm"
include "2cnd.mm"
include "adantl.mm"
include "mulassd.mm"
include "3eqtrd.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "impr.mm"
include "rexlimiva.mm"
include "impbid1.mm"

theorem perfectALTV
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x

  disjoint N p
  disjoint k x
  assert |- ( ( N e. NN /\ N e. Even ) -> ( ( 1 sigma N ) = ( 2 x. N ) <-> E. p e. ZZ ( ( ( 2 ^ p ) - 1 ) e. Prime /\ N = ( ( 2 ^ ( p - 1 ) ) x. ( ( 2 ^ p ) - 1 ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    ceven
    wcel
    #
    wa
    #
    c1
    cN
    csgm
    co
    #
    c2
    cN
    cmul
    co
    #
    wceq
    #
    c2
    vp
    cv
    #
    cexp
    co
    #
    c1
    cmin
    co
    #
    cprime
    wcel
    #
    cN
    c2
    @6
    c1
    cmin
    co
    #
    cexp
    co
    #
    @8
    cmul
    co
    #
    wceq
    #
    wa
    #
    vp
    cz
    wrex
    #
    @2
    @5
    @15
    @2
    @5
    wa
    #
    c2
    cN
    cpc
    co
    #
    c1
    caddc
    co
    #
    cz
    wcel
    c2
    @18
    cexp
    co
    #
    c1
    cmin
    co
    #
    cprime
    wcel
    #
    cN
    c2
    @18
    c1
    cmin
    co
    #
    cexp
    co
    #
    @20
    cmul
    co
    #
    wceq
    #
    @15
    @16
    @17
    @16
    @17
    @16
    @17
    cn
    wcel
    #
    c2
    cN
    cdvds
    wbr
    #
    @1
    @27
    @0
    @5
    cN
    2dvdseven
    ad2antlr
    @16
    c2
    cprime
    wcel
    #
    @0
    @26
    @27
    wb
    2prm
    @0
    @1
    @5
    simpll
    #
    c2
    cN
    pcelnn
    sylancr
    mpbird
    #
    nnzd
    peano2zd
    @16
    cN
    c2
    @17
    cexp
    co
    #
    cdiv
    co
    #
    @20
    cprime
    @16
    @32
    cprime
    wcel
    #
    @32
    @20
    wceq
    #
    @16
    @17
    @32
    @30
    @16
    @31
    cN
    cdvds
    wbr
    #
    @32
    cn
    wcel
    #
    @16
    @28
    @0
    @35
    2prm
    @29
    c2
    cN
    pcdvds
    sylancr
    @16
    @0
    @31
    cn
    wcel
    #
    @35
    @36
    wb
    @29
    @16
    c2
    cn
    wcel
    @17
    cn0
    wcel
    @37
    2nn
    @16
    @17
    @30
    nnnn0d
    c2
    @17
    nnexpcl
    sylancr
    #
    cN
    @31
    nndivdvds
    syl2anc
    mpbid
    #
    @16
    @32
    cz
    wcel
    c2
    @32
    cdvds
    wbr
    wn
    #
    @32
    codd
    wcel
    @16
    @32
    @39
    nnzd
    @16
    @28
    @0
    @40
    2prm
    @29
    c2
    cN
    pcndvds2
    sylancr
    @32
    isodd3
    sylanbrc
    @16
    @3
    @4
    c1
    @31
    @32
    cmul
    co
    #
    csgm
    co
    c2
    @41
    cmul
    co
    @2
    @5
    simpr
    @16
    @41
    cN
    c1
    csgm
    @16
    cN
    @31
    @0
    cN
    cc
    wcel
    @1
    @5
    cN
    nncn
    ad2antrr
    @16
    @31
    @38
    nncnd
    @16
    @31
    @38
    nnne0d
    divcan2d
    #
    oveq2d
    @16
    @41
    cN
    c2
    cmul
    @42
    oveq2d
    3eqtr4d
    perfectALTVlem2
    #
    simprd
    #
    @16
    @33
    @34
    @43
    simpld
    eqeltrrd
    @16
    @41
    cN
    @24
    @42
    @16
    @31
    @23
    @32
    @20
    cmul
    @16
    @17
    @22
    c2
    cexp
    @16
    @22
    @17
    @16
    @17
    cc
    wcel
    c1
    cc
    wcel
    @22
    @17
    wceq
    @16
    @17
    @30
    nncnd
    ax-1cn
    @17
    c1
    pncan
    sylancl
    eqcomd
    oveq2d
    @44
    oveq12d
    eqtr3d
    @14
    @21
    @25
    wa
    vp
    @18
    cz
    @6
    @18
    wceq
    #
    @9
    @21
    @13
    @25
    @45
    @8
    @20
    cprime
    @45
    @7
    @19
    c1
    cmin
    @6
    @18
    c2
    cexp
    oveq2
    oveq1d
    #
    eleq1d
    @45
    @12
    @24
    cN
    @45
    @11
    @23
    @8
    @20
    cmul
    @45
    @10
    @22
    c2
    cexp
    @6
    @18
    c1
    cmin
    oveq1
    oveq2d
    @46
    oveq12d
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    ex
    @14
    @5
    vp
    cz
    @6
    cz
    wcel
    #
    @9
    @13
    @5
    @47
    @9
    wa
    #
    @5
    @13
    c1
    @12
    csgm
    co
    #
    c2
    @12
    cmul
    co
    #
    wceq
    @48
    @49
    @7
    @8
    cmul
    co
    c2
    @11
    cmul
    co
    #
    @8
    cmul
    co
    @50
    @6
    perfect1
    @48
    @7
    @51
    @8
    cmul
    @48
    @7
    @11
    c2
    cmul
    co
    #
    @51
    @48
    c2
    cc
    wcel
    #
    @6
    cn
    wcel
    #
    @7
    @52
    wceq
    2cn
    @48
    @6
    cprime
    wcel
    @54
    @6
    mersenne
    @6
    prmnn
    syl
    #
    c2
    @6
    expm1t
    sylancr
    @48
    @11
    cc
    wcel
    #
    @53
    @52
    @51
    wceq
    @48
    @53
    @10
    cn0
    wcel
    #
    @56
    2cn
    @48
    @54
    @57
    @55
    @6
    nnm1nn0
    syl
    c2
    @10
    expcl
    sylancr
    #
    2cn
    @11
    c2
    mulcom
    sylancl
    eqtrd
    oveq1d
    @48
    c2
    @11
    @8
    @48
    2cnd
    @58
    @48
    @8
    @9
    @8
    cn
    wcel
    @47
    @8
    prmnn
    adantl
    nncnd
    mulassd
    3eqtrd
    @13
    @3
    @49
    @4
    @50
    cN
    @12
    c1
    csgm
    oveq2
    cN
    @12
    c2
    cmul
    oveq2
    eqeq12d
    syl5ibrcom
    impr
    rexlimiva
    impbid1
end
