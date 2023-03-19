include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "csgm.mm"
include "co.mm"
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
include "simplr.mm"
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
include "pcndvds2.mm"
include "simpr.mm"
include "cc.mm"
include "nncn.mm"
include "ad2antrr.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "perfectlem2.mm"
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

theorem perfect
  let cN: class N
  let vp: setvar p

  disjoint N p
  assert |- ( ( N e. NN /\ 2 || N ) -> ( ( 1 sigma N ) = ( 2 x. N ) <-> E. p e. ZZ ( ( ( 2 ^ p ) - 1 ) e. Prime /\ N = ( ( 2 ^ ( p - 1 ) ) x. ( ( 2 ^ p ) - 1 ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
    c2
    cN
    cdvds
    wbr
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
    @1
    @0
    @1
    @5
    simplr
    @16
    c2
    cprime
    wcel
    #
    @0
    @26
    @1
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
    @31
    cprime
    wcel
    #
    @31
    @20
    wceq
    #
    @16
    @17
    @31
    @29
    @16
    @30
    cN
    cdvds
    wbr
    #
    @31
    cn
    wcel
    #
    @16
    @27
    @0
    @34
    2prm
    @28
    c2
    cN
    pcdvds
    sylancr
    @16
    @0
    @30
    cn
    wcel
    #
    @34
    @35
    wb
    @28
    @16
    c2
    cn
    wcel
    @17
    cn0
    wcel
    @36
    2nn
    @16
    @17
    @29
    nnnn0d
    c2
    @17
    nnexpcl
    sylancr
    #
    cN
    @30
    nndivdvds
    syl2anc
    mpbid
    @16
    @27
    @0
    c2
    @31
    cdvds
    wbr
    wn
    2prm
    @28
    c2
    cN
    pcndvds2
    sylancr
    @16
    @3
    @4
    c1
    @30
    @31
    cmul
    co
    #
    csgm
    co
    c2
    @38
    cmul
    co
    @2
    @5
    simpr
    @16
    @38
    cN
    c1
    csgm
    @16
    cN
    @30
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
    @30
    @37
    nncnd
    @16
    @30
    @37
    nnne0d
    divcan2d
    #
    oveq2d
    @16
    @38
    cN
    c2
    cmul
    @39
    oveq2d
    3eqtr4d
    perfectlem2
    #
    simprd
    #
    @16
    @32
    @33
    @40
    simpld
    eqeltrrd
    @16
    @38
    cN
    @24
    @39
    @16
    @30
    @23
    @31
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
    @29
    nncnd
    ax-1cn
    @17
    c1
    pncan
    sylancl
    eqcomd
    oveq2d
    @41
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
    @42
    @8
    @20
    cprime
    @42
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
    @42
    @12
    @24
    cN
    @42
    @11
    @23
    @8
    @20
    cmul
    @42
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
    @43
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
    @44
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
    @45
    @46
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
    @47
    @6
    perfect1
    @45
    @7
    @48
    @8
    cmul
    @45
    @7
    @11
    c2
    cmul
    co
    #
    @48
    @45
    c2
    cc
    wcel
    #
    @6
    cn
    wcel
    #
    @7
    @49
    wceq
    2cn
    @45
    @6
    cprime
    wcel
    @51
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
    @45
    @11
    cc
    wcel
    #
    @50
    @49
    @48
    wceq
    @45
    @50
    @10
    cn0
    wcel
    #
    @53
    2cn
    @45
    @51
    @54
    @52
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
    @45
    c2
    @11
    @8
    @45
    2cnd
    @55
    @45
    @8
    @9
    @8
    cn
    wcel
    @44
    @8
    prmnn
    adantl
    nncnd
    mulassd
    3eqtrd
    @13
    @3
    @46
    @4
    @47
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
