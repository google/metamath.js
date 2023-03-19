include "ci.mm"
include "cabs.mm"
include "cfv.mm"
include "ccj.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "c1.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "ax-icn.mm"
include "absval.mm"
include "ax-mp.mm"
include "cneg.mm"
include "cji.mm"
include "oveq2i.mm"
include "mulneg2i.mm"
include "ixi.mm"
include "negeqi.mm"
include "negneg1e1.mm"
include "eqtri.mm"
include "3eqtri.mm"
include "fveq2i.mm"
include "sqrt1.mm"

theorem absi



  assert |- ( abs ` _i ) = 1

  proof
    ci
    cabs
    cfv
    #
    ci
    ci
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    c1
    csqrt
    cfv
    c1
    ci
    cc
    wcel
    @0
    @3
    wceq
    ax-icn
    ci
    absval
    ax-mp
    @2
    c1
    csqrt
    @2
    ci
    ci
    cneg
    #
    cmul
    co
    ci
    ci
    cmul
    co
    #
    cneg
    #
    c1
    @1
    @4
    ci
    cmul
    cji
    oveq2i
    ci
    ci
    ax-icn
    ax-icn
    mulneg2i
    @6
    c1
    cneg
    #
    cneg
    c1
    @5
    @7
    ixi
    negeqi
    negneg1e1
    eqtri
    3eqtri
    fveq2i
    sqrt1
    3eqtri
end
