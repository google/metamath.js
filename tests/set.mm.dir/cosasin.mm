include "cc.mm"
include "wcel.mm"
include "casin.mm"
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
include "cmin.mm"
include "csqrt.mm"
include "wceq.mm"
include "asincl.mm"
include "cosval.mm"
include "syl.mm"
include "ax-1cn.mm"
include "sqcl.mm"
include "subcl.mm"
include "sylancr.mm"
include "sqrtcld.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "ppncand.mm"
include "efiasin.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "mulneg12.mm"
include "asinneg.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "negcl.mm"
include "mulneg2.mm"
include "sqneg.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "negcld.mm"
include "negsubd.mm"
include "2timesd.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan3d.mm"

theorem cosasin
  let cA: class A


  assert |- ( A e. CC -> ( cos ` ( arcsin ` A ) ) = ( sqrt ` ( 1 - ( A ^ 2 ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    casin
    cfv
    #
    ccos
    cfv
    #
    ci
    @1
    cmul
    co
    ce
    cfv
    #
    ci
    cneg
    @1
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
    cmin
    co
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    c2
    cdiv
    co
    @10
    @0
    @1
    cc
    wcel
    #
    @2
    @7
    wceq
    cA
    asincl
    #
    @1
    cosval
    syl
    @0
    @6
    @11
    c2
    cdiv
    @0
    @10
    ci
    cA
    cmul
    co
    #
    caddc
    co
    #
    @10
    @14
    cmin
    co
    #
    caddc
    co
    @10
    @10
    caddc
    co
    @6
    @11
    @0
    @10
    @14
    @10
    @0
    @9
    @0
    c1
    cc
    wcel
    @8
    cc
    wcel
    @9
    cc
    wcel
    ax-1cn
    cA
    sqcl
    c1
    @8
    subcl
    sylancr
    sqrtcld
    #
    ci
    cc
    wcel
    #
    @0
    @14
    cc
    wcel
    ax-icn
    ci
    cA
    mulcl
    mpan
    #
    @17
    ppncand
    @0
    @3
    @15
    @5
    @16
    caddc
    @0
    @3
    @14
    @10
    caddc
    co
    @15
    cA
    efiasin
    @0
    @14
    @10
    @19
    @17
    addcomd
    eqtrd
    @0
    @5
    @14
    cneg
    #
    @10
    caddc
    co
    #
    @10
    @20
    caddc
    co
    @16
    @0
    @5
    ci
    cA
    cneg
    #
    casin
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    ci
    @22
    cmul
    co
    #
    c1
    @22
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    @21
    @0
    @4
    @24
    ce
    @0
    @4
    ci
    @1
    cneg
    #
    cmul
    co
    #
    @24
    @0
    @18
    @12
    @4
    @32
    wceq
    ax-icn
    @13
    ci
    @1
    mulneg12
    sylancr
    @0
    @23
    @31
    ci
    cmul
    cA
    asinneg
    oveq2d
    eqtr4d
    fveq2d
    @0
    @22
    cc
    wcel
    @25
    @30
    wceq
    cA
    negcl
    @22
    efiasin
    syl
    @0
    @26
    @20
    @29
    @10
    caddc
    @18
    @0
    @26
    @20
    wceq
    ax-icn
    ci
    cA
    mulneg2
    mpan
    @0
    @28
    @9
    csqrt
    @0
    @27
    @8
    c1
    cmin
    cA
    sqneg
    oveq2d
    fveq2d
    oveq12d
    3eqtrd
    @0
    @20
    @10
    @0
    @14
    @19
    negcld
    @17
    addcomd
    @0
    @10
    @14
    @17
    @19
    negsubd
    3eqtrd
    oveq12d
    @0
    @10
    @17
    2timesd
    3eqtr4d
    oveq1d
    @0
    @10
    c2
    @17
    @0
    2cnd
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    divcan3d
    3eqtrd
end
