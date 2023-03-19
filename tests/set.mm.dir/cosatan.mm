include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "ccos.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cneg.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "c1.mm"
include "cexp.mm"
include "csqrt.mm"
include "cc.mm"
include "wceq.mm"
include "atancl.mm"
include "cosval.mm"
include "syl.mm"
include "cmin.mm"
include "efiatan2.mm"
include "ax-icn.mm"
include "mulneg12.mm"
include "sylancr.mm"
include "atanneg.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "atandmneg.mm"
include "cc0.mm"
include "wne.mm"
include "atandm4.mm"
include "simplbi.mm"
include "mulneg2.mm"
include "ax-1cn.mm"
include "mulcl.mm"
include "negsub.mm"
include "eqtrd.mm"
include "sqneg.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "addcl.mm"
include "subcl.mm"
include "sqcld.mm"
include "sqrtcld.mm"
include "sqsqrtd.mm"
include "simprbi.mm"
include "eqnetrd.mm"
include "wb.mm"
include "sqne0.mm"
include "mpbid.mm"
include "divdird.mm"
include "a1i.mm"
include "ppncand.mm"
include "df-2.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "2cnd.mm"
include "2ne0.mm"
include "divdiv32d.mm"
include "2div2e1.mm"
include "oveq1i.mm"
include "syl6eq.mm"

theorem cosatan
  let cA: class A


  assert |- ( A e. dom arctan -> ( cos ` ( arctan ` A ) ) = ( 1 / ( sqrt ` ( 1 + ( A ^ 2 ) ) ) ) )

  proof
    cA
    catan
    cdm
    #
    wcel
    #
    cA
    catan
    cfv
    #
    ccos
    cfv
    #
    ci
    @2
    cmul
    co
    ce
    cfv
    #
    ci
    cneg
    @2
    cmul
    co
    #
    ce
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
    c1
    cA
    c2
    cexp
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    c1
    @11
    cdiv
    co
    #
    @1
    @2
    cc
    wcel
    #
    @3
    @8
    wceq
    cA
    atancl
    #
    @2
    cosval
    syl
    @1
    @7
    @12
    c2
    cdiv
    @1
    @7
    c1
    ci
    cA
    cmul
    co
    #
    caddc
    co
    #
    @11
    cdiv
    co
    #
    c1
    @17
    cmin
    co
    #
    @11
    cdiv
    co
    #
    caddc
    co
    @18
    @20
    caddc
    co
    #
    @11
    cdiv
    co
    @12
    @1
    @4
    @19
    @6
    @21
    caddc
    cA
    efiatan2
    @1
    @6
    ci
    cA
    cneg
    #
    catan
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    c1
    ci
    @23
    cmul
    co
    #
    caddc
    co
    #
    c1
    @23
    c2
    cexp
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    @21
    @1
    @5
    @25
    ce
    @1
    @5
    ci
    @2
    cneg
    #
    cmul
    co
    #
    @25
    @1
    ci
    cc
    wcel
    #
    @15
    @5
    @34
    wceq
    ax-icn
    @16
    ci
    @2
    mulneg12
    sylancr
    @1
    @24
    @33
    ci
    cmul
    cA
    atanneg
    oveq2d
    eqtr4d
    fveq2d
    @1
    @23
    @0
    wcel
    @26
    @32
    wceq
    cA
    atandmneg
    @23
    efiatan2
    syl
    @1
    @28
    @20
    @31
    @11
    cdiv
    @1
    @28
    c1
    @17
    cneg
    #
    caddc
    co
    #
    @20
    @1
    @27
    @36
    c1
    caddc
    @1
    @35
    cA
    cc
    wcel
    #
    @27
    @36
    wceq
    ax-icn
    @1
    @38
    @10
    cc0
    wne
    #
    cA
    atandm4
    #
    simplbi
    #
    ci
    cA
    mulneg2
    sylancr
    oveq2d
    @1
    c1
    cc
    wcel
    #
    @17
    cc
    wcel
    #
    @37
    @20
    wceq
    ax-1cn
    @1
    @35
    @38
    @43
    ax-icn
    @41
    ci
    cA
    mulcl
    sylancr
    #
    c1
    @17
    negsub
    sylancr
    eqtrd
    @1
    @30
    @10
    csqrt
    @1
    @29
    @9
    c1
    caddc
    @1
    @38
    @29
    @9
    wceq
    @41
    cA
    sqneg
    syl
    oveq2d
    fveq2d
    oveq12d
    3eqtrd
    oveq12d
    @1
    @18
    @20
    @11
    @1
    @42
    @43
    @18
    cc
    wcel
    ax-1cn
    @44
    c1
    @17
    addcl
    sylancr
    @1
    @42
    @43
    @20
    cc
    wcel
    ax-1cn
    @44
    c1
    @17
    subcl
    sylancr
    @1
    @10
    @1
    @42
    @9
    cc
    wcel
    @10
    cc
    wcel
    ax-1cn
    @1
    cA
    @41
    sqcld
    c1
    @9
    addcl
    sylancr
    #
    sqrtcld
    #
    @1
    @11
    c2
    cexp
    co
    #
    cc0
    wne
    #
    @11
    cc0
    wne
    #
    @1
    @47
    @10
    cc0
    @1
    @10
    @45
    sqsqrtd
    @1
    @38
    @39
    @40
    simprbi
    eqnetrd
    @1
    @11
    cc
    wcel
    @48
    @49
    wb
    @46
    @11
    sqne0
    syl
    mpbid
    #
    divdird
    @1
    @22
    c2
    @11
    cdiv
    @1
    @22
    c1
    c1
    caddc
    co
    c2
    @1
    c1
    @17
    c1
    @42
    @1
    ax-1cn
    a1i
    #
    @44
    @51
    ppncand
    df-2
    syl6eqr
    oveq1d
    3eqtr2d
    oveq1d
    @1
    @13
    c2
    c2
    cdiv
    co
    #
    @11
    cdiv
    co
    @14
    @1
    c2
    @11
    c2
    @1
    2cnd
    #
    @46
    @53
    @50
    c2
    cc0
    wne
    @1
    2ne0
    a1i
    divdiv32d
    @52
    c1
    @11
    cdiv
    2div2e1
    oveq1i
    syl6eq
    3eqtrd
end
