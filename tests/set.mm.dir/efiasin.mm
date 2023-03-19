include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "casin.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "csqrt.mm"
include "caddc.mm"
include "clog.mm"
include "cneg.mm"
include "asinval.mm"
include "oveq2d.mm"
include "ax-icn.mm"
include "a1i.mm"
include "negicn.mm"
include "mulcl.mm"
include "mpan.mm"
include "ax-1cn.mm"
include "sqcl.mm"
include "subcl.mm"
include "sylancr.mm"
include "sqrtcld.mm"
include "addcld.mm"
include "asinlem.mm"
include "logcld.mm"
include "mulassd.mm"
include "mulneg2i.mm"
include "ixi.mm"
include "negeqi.mm"
include "negneg1e1.mm"
include "3eqtri.mm"
include "oveq1i.mm"
include "mulid2d.mm"
include "syl5eq.mm"
include "3eqtr2d.mm"
include "fveq2d.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "eflog.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem efiasin
  let cA: class A


  assert |- ( A e. CC -> ( exp ` ( _i x. ( arcsin ` A ) ) ) = ( ( _i x. A ) + ( sqrt ` ( 1 - ( A ^ 2 ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    ci
    cA
    casin
    cfv
    #
    cmul
    co
    #
    ce
    cfv
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
    clog
    cfv
    #
    ce
    cfv
    #
    @7
    @0
    @2
    @8
    ce
    @0
    @2
    ci
    ci
    cneg
    #
    @8
    cmul
    co
    #
    cmul
    co
    ci
    @10
    cmul
    co
    #
    @8
    cmul
    co
    #
    @8
    @0
    @1
    @11
    ci
    cmul
    cA
    asinval
    oveq2d
    @0
    ci
    @10
    @8
    ci
    cc
    wcel
    #
    @0
    ax-icn
    a1i
    @10
    cc
    wcel
    @0
    negicn
    a1i
    @0
    @7
    @0
    @3
    @6
    @14
    @0
    @3
    cc
    wcel
    ax-icn
    ci
    cA
    mulcl
    mpan
    @0
    @5
    @0
    c1
    cc
    wcel
    @4
    cc
    wcel
    @5
    cc
    wcel
    ax-1cn
    cA
    sqcl
    c1
    @4
    subcl
    sylancr
    sqrtcld
    addcld
    #
    cA
    asinlem
    #
    logcld
    #
    mulassd
    @0
    @13
    c1
    @8
    cmul
    co
    @8
    @12
    c1
    @8
    cmul
    @12
    ci
    ci
    cmul
    co
    #
    cneg
    c1
    cneg
    #
    cneg
    c1
    ci
    ci
    ax-icn
    ax-icn
    mulneg2i
    @18
    @19
    ixi
    negeqi
    negneg1e1
    3eqtri
    oveq1i
    @0
    @8
    @17
    mulid2d
    syl5eq
    3eqtr2d
    fveq2d
    @0
    @7
    cc
    wcel
    @7
    cc0
    wne
    @9
    @7
    wceq
    @15
    @16
    @7
    eflog
    syl2anc
    eqtrd
end
