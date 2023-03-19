include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "ccxp.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "rpcn.mm"
include "adantr.mm"
include "rpne0.mm"
include "simpr.mm"
include "recnd.mm"
include "cxpef.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "id.mm"
include "relogcl.mm"
include "remulcl.mm"
include "syl2anr.mm"
include "relogefd.mm"
include "eqtrd.mm"

theorem logcxp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR ) -> ( log ` ( A ^c B ) ) = ( B x. ( log ` A ) ) )

  proof
    cA
    crp
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    ccxp
    co
    #
    clog
    cfv
    cB
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    clog
    cfv
    @5
    @2
    @3
    @6
    clog
    @2
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cB
    cc
    wcel
    @3
    @6
    wceq
    @0
    @7
    @1
    cA
    rpcn
    adantr
    @0
    @8
    @1
    cA
    rpne0
    adantr
    @2
    cB
    @0
    @1
    simpr
    recnd
    cA
    cB
    cxpef
    syl3anc
    fveq2d
    @2
    @5
    @1
    @1
    @4
    cr
    wcel
    @5
    cr
    wcel
    @0
    @1
    id
    cA
    relogcl
    cB
    @4
    remulcl
    syl2anr
    relogefd
    eqtrd
end
