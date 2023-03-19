include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "crest.mm"
include "co.mm"
include "cperf.mm"
include "elpri.mm"
include "oveq2.mm"
include "reperf.mm"
include "syl6eqel.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "cnperf.mm"
include "eqeltri.mm"
include "jaoi.mm"
include "syl.mm"

theorem recnperf
  let cS: class S
  let cK: class K
  assume recnperf.k: |- K = ( TopOpen ` CCfld )


  assert |- ( S e. { RR , CC } -> ( K |`t S ) e. Perf )

  proof
    cS
    cr
    cc
    cpr
    wcel
    cS
    cr
    wceq
    #
    cS
    cc
    wceq
    #
    wo
    cK
    cS
    crest
    co
    #
    cperf
    wcel
    #
    cS
    cr
    cc
    elpri
    @0
    @3
    @1
    @0
    @2
    cK
    cr
    crest
    co
    cperf
    cS
    cr
    cK
    crest
    oveq2
    cK
    recnperf.k
    reperf
    syl6eqel
    @1
    @2
    cK
    cc
    crest
    co
    #
    cperf
    cS
    cc
    cK
    crest
    oveq2
    @4
    cK
    cperf
    cK
    cc
    ctopon
    cfv
    #
    wcel
    @4
    cK
    wceq
    cK
    recnperf.k
    cnfldtopon
    #
    cK
    @5
    cc
    cc
    cK
    @6
    toponunii
    restid
    ax-mp
    cK
    recnperf.k
    cnperf
    eqeltri
    syl6eqel
    jaoi
    syl
end
