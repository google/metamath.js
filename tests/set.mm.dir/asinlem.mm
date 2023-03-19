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
include "cneg.mm"
include "caddc.mm"
include "cc0.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "ax-1cn.mm"
include "sqcl.mm"
include "subcl.mm"
include "sylancr.mm"
include "sqrtcld.mm"
include "subnegd.mm"
include "negcld.mm"
include "wne.mm"
include "0ne1.mm"
include "wb.mm"
include "0cnd.mm"
include "1cnd.mm"
include "w3a.mm"
include "subcan2.mm"
include "necon3bid.mm"
include "syl3anc.mm"
include "mpbiri.mm"
include "wceq.mm"
include "sqmul.mm"
include "i2.mm"
include "oveq1i.mm"
include "mulm1d.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "df-neg.mm"
include "syl6eq.mm"
include "sqneg.mm"
include "syl.mm"
include "sqsqrtd.mm"
include "3netr4d.mm"
include "oveq1.mm"
include "necon3i.mm"
include "subne0d.mm"
include "eqnetrrd.mm"

theorem asinlem
  let cA: class A


  assert |- ( A e. CC -> ( ( _i x. A ) + ( sqrt ` ( 1 - ( A ^ 2 ) ) ) ) =/= 0 )

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
    cneg
    #
    cmin
    co
    @1
    @4
    caddc
    co
    cc0
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
    subnegd
    @0
    @1
    @5
    @7
    @0
    @4
    @12
    negcld
    @0
    @1
    c2
    cexp
    co
    #
    @5
    c2
    cexp
    co
    #
    wne
    @1
    @5
    wne
    @0
    cc0
    @2
    cmin
    co
    #
    @3
    @13
    @14
    @0
    @15
    @3
    wne
    #
    cc0
    c1
    wne
    #
    0ne1
    @0
    cc0
    cc
    wcel
    #
    @8
    @9
    @16
    @17
    wb
    @0
    0cnd
    @0
    1cnd
    @10
    @18
    @8
    @9
    w3a
    @15
    @3
    cc0
    c1
    cc0
    c1
    @2
    subcan2
    necon3bid
    syl3anc
    mpbiri
    @0
    @13
    @2
    cneg
    #
    @15
    @0
    @13
    ci
    c2
    cexp
    co
    #
    @2
    cmul
    co
    #
    @19
    @6
    @0
    @13
    @21
    wceq
    ax-icn
    ci
    cA
    sqmul
    mpan
    @0
    @21
    c1
    cneg
    #
    @2
    cmul
    co
    @19
    @20
    @22
    @2
    cmul
    i2
    oveq1i
    @0
    @2
    @10
    mulm1d
    syl5eq
    eqtrd
    @2
    df-neg
    syl6eq
    @0
    @14
    @4
    c2
    cexp
    co
    #
    @3
    @0
    @4
    cc
    wcel
    @14
    @23
    wceq
    @12
    @4
    sqneg
    syl
    @0
    @3
    @11
    sqsqrtd
    eqtrd
    3netr4d
    @1
    @5
    @13
    @14
    @1
    @5
    c2
    cexp
    oveq1
    necon3i
    syl
    subne0d
    eqnetrrd
end
