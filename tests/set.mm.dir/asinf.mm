include "cc.mm"
include "ci.mm"
include "cneg.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "csqrt.mm"
include "cfv.mm"
include "caddc.mm"
include "clog.mm"
include "casin.mm"
include "df-asin.mm"
include "wcel.mm"
include "negicn.mm"
include "ax-icn.mm"
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
include "fmpti.mm"

theorem asinf
  let vx: setvar x


  assert |- arcsin : CC --> CC

  proof
    vx
    cc
    cc
    ci
    cneg
    #
    ci
    vx
    cv
    #
    cmul
    co
    #
    c1
    @1
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
    cmul
    co
    #
    casin
    vx
    df-asin
    @1
    cc
    wcel
    #
    @0
    cc
    wcel
    @7
    cc
    wcel
    @8
    cc
    wcel
    negicn
    @9
    @6
    @9
    @2
    @5
    ci
    cc
    wcel
    @9
    @2
    cc
    wcel
    ax-icn
    ci
    @1
    mulcl
    mpan
    @9
    @4
    @9
    c1
    cc
    wcel
    @3
    cc
    wcel
    @4
    cc
    wcel
    ax-1cn
    @1
    sqcl
    c1
    @3
    subcl
    sylancr
    sqrtcld
    addcld
    @1
    asinlem
    logcld
    @0
    @7
    mulcl
    sylancr
    fmpti
end
