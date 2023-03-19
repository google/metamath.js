include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "ccxp.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "cxpef.mm"
include "wa.mm"
include "id.mm"
include "logcl.mm"
include "mulcl.mm"
include "syl2anr.mm"
include "3impa.mm"
include "efne0.mm"
include "syl.mm"
include "eqnetrd.mm"

theorem cxpne0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ A =/= 0 /\ B e. CC ) -> ( A ^c B ) =/= 0 )

  proof
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
    #
    w3a
    #
    cA
    cB
    ccxp
    co
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
    cc0
    cA
    cB
    cxpef
    @3
    @5
    cc
    wcel
    #
    @6
    cc0
    wne
    @0
    @1
    @2
    @7
    @2
    @2
    @4
    cc
    wcel
    @7
    @0
    @1
    wa
    @2
    id
    cA
    logcl
    cB
    @4
    mulcl
    syl2anr
    3impa
    @5
    efne0
    syl
    eqnetrd
end
