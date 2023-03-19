include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "cpthson.mm"
include "co.mm"
include "chash.mm"
include "cpths.mm"
include "cyclispth.mm"
include "pthonpth.mm"
include "syl.mm"
include "wceq.mm"
include "wa.mm"
include "iscycl.mm"
include "simpr.mm"
include "sylbi.mm"
include "oveq2d.mm"
include "breqd.mm"
include "mpbird.mm"

theorem cyclispthon
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Cycles ` G ) P -> F ( ( P ` 0 ) ( PathsOn ` G ) ( P ` 0 ) ) P )

  proof
    cF
    cP
    cG
    ccycls
    cfv
    wbr
    #
    cF
    cP
    cc0
    cP
    cfv
    #
    @1
    cG
    cpthson
    cfv
    #
    co
    #
    wbr
    cF
    cP
    @1
    cF
    chash
    cfv
    cP
    cfv
    #
    @2
    co
    #
    wbr
    #
    @0
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    @6
    cP
    cF
    cG
    cyclispth
    cP
    cF
    cG
    pthonpth
    syl
    @0
    @3
    @5
    cF
    cP
    @0
    @1
    @4
    @1
    @2
    @0
    @7
    @1
    @4
    wceq
    #
    wa
    @8
    cP
    cF
    cG
    iscycl
    @7
    @8
    simpr
    sylbi
    oveq2d
    breqd
    mpbird
end
