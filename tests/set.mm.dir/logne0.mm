include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "wa.mm"
include "cc.mm"
include "cc0.mm"
include "clog.mm"
include "cfv.mm"
include "rpcn.mm"
include "adantr.mm"
include "rpne0.mm"
include "simpr.mm"
include "logccne0.mm"
include "syl3anc.mm"

theorem logne0
  let cA: class A


  assert |- ( ( A e. RR+ /\ A =/= 1 ) -> ( log ` A ) =/= 0 )

  proof
    cA
    crp
    wcel
    #
    cA
    c1
    wne
    #
    wa
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    @1
    cA
    clog
    cfv
    cc0
    wne
    @0
    @2
    @1
    cA
    rpcn
    adantr
    @0
    @3
    @1
    cA
    rpne0
    adantr
    @0
    @1
    simpr
    cA
    logccne0
    syl3anc
end
