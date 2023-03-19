include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "csqrt.mm"
include "cfv.mm"
include "caddc.mm"
include "cneg.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "ax-1cn.mm"
include "sqcl.mm"
include "subcl.mm"
include "sylancr.mm"
include "sqrtcld.mm"
include "addcomd.mm"
include "wceq.mm"
include "mulneg2.mm"
include "sqneg.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "negcld.mm"
include "negsubd.mm"
include "3eqtrd.mm"
include "sqsqrtd.mm"
include "sqmul.mm"
include "i2.mm"
include "oveq1i.mm"
include "mulm1d.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "subsq.mm"
include "syl2anc.mm"
include "subnegd.mm"
include "3eqtr3d.mm"
include "npcan.mm"

theorem asinlem2
  let cA: class A


  assert |- ( A e. CC -> ( ( ( _i x. A ) + ( sqrt ` ( 1 - ( A ^ 2 ) ) ) ) x. ( ( _i x. -u A ) + ( sqrt ` ( 1 - ( -u A ^ 2 ) ) ) ) ) = 1 )

  proof
    cA
    cc
    wcel
    #
    ci
    cA
    cmul
    co
    #
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
    caddc
    co
    #
    ci
    cA
    cneg
    #
    cmul
    co
    #
    c1
    @6
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
    cmul
    co
    @4
    @1
    caddc
    co
    #
    @4
    @1
    cmin
    co
    #
    cmul
    co
    #
    @3
    @2
    caddc
    co
    #
    c1
    @0
    @5
    @12
    @11
    @13
    cmul
    @0
    @1
    @4
    ci
    cc
    wcel
    #
    @0
    @1
    cc
    wcel
    #
    ax-icn
    ci
    cA
    mulcl
    mpan
    #
    @0
    @3
    @0
    c1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @3
    cc
    wcel
    ax-1cn
    cA
    sqcl
    #
    c1
    @2
    subcl
    sylancr
    #
    sqrtcld
    #
    addcomd
    @0
    @11
    @1
    cneg
    #
    @4
    caddc
    co
    @4
    @24
    caddc
    co
    @13
    @0
    @7
    @24
    @10
    @4
    caddc
    @16
    @0
    @7
    @24
    wceq
    ax-icn
    ci
    cA
    mulneg2
    mpan
    @0
    @9
    @3
    csqrt
    @0
    @8
    @2
    c1
    cmin
    cA
    sqneg
    oveq2d
    fveq2d
    oveq12d
    @0
    @24
    @4
    @0
    @1
    @18
    negcld
    @23
    addcomd
    @0
    @4
    @1
    @23
    @18
    negsubd
    3eqtrd
    oveq12d
    @0
    @4
    c2
    cexp
    co
    #
    @1
    c2
    cexp
    co
    #
    cmin
    co
    #
    @3
    @2
    cneg
    #
    cmin
    co
    @14
    @15
    @0
    @25
    @3
    @26
    @28
    cmin
    @0
    @3
    @22
    sqsqrtd
    @0
    @26
    ci
    c2
    cexp
    co
    #
    @2
    cmul
    co
    #
    @28
    @16
    @0
    @26
    @30
    wceq
    ax-icn
    ci
    cA
    sqmul
    mpan
    @0
    @30
    c1
    cneg
    #
    @2
    cmul
    co
    @28
    @29
    @31
    @2
    cmul
    i2
    oveq1i
    @0
    @2
    @21
    mulm1d
    syl5eq
    eqtrd
    oveq12d
    @0
    @4
    cc
    wcel
    @17
    @27
    @14
    wceq
    @23
    @18
    @4
    @1
    subsq
    syl2anc
    @0
    @3
    @2
    @22
    @21
    subnegd
    3eqtr3d
    @0
    @19
    @20
    @15
    c1
    wceq
    ax-1cn
    @21
    c1
    @2
    npcan
    sylancr
    3eqtrd
end
