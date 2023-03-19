include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "ccxp.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cif.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "cxpval.mm"
include "3adant2.mm"
include "simp2.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem cxpef
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ A =/= 0 /\ B e. CC ) -> ( A ^c B ) = ( exp ` ( B x. ( log ` A ) ) ) )

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
    #
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    c1
    cc0
    cif
    #
    cB
    cA
    clog
    cfv
    cmul
    co
    ce
    cfv
    #
    cif
    #
    @7
    @0
    @2
    @4
    @8
    wceq
    @1
    cA
    cB
    cxpval
    3adant2
    @3
    @5
    @6
    @7
    @3
    cA
    cc0
    @0
    @1
    @2
    simp2
    neneqd
    iffalsed
    eqtrd
end
