include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "ccxp.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "ax-1cn.mm"
include "cxpadd.mm"
include "mp3an3.mm"
include "3impa.mm"
include "cxp1.mm"
include "3ad2ant1.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem cxpp1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ A =/= 0 /\ B e. CC ) -> ( A ^c ( B + 1 ) ) = ( ( A ^c B ) x. A ) )

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
    c1
    caddc
    co
    ccxp
    co
    #
    cA
    cB
    ccxp
    co
    #
    cA
    c1
    ccxp
    co
    #
    cmul
    co
    #
    @5
    cA
    cmul
    co
    @0
    @1
    @2
    @4
    @7
    wceq
    #
    @0
    @1
    wa
    @2
    c1
    cc
    wcel
    @8
    ax-1cn
    cA
    cB
    c1
    cxpadd
    mp3an3
    3impa
    @3
    @6
    cA
    @5
    cmul
    @0
    @1
    @6
    cA
    wceq
    @2
    cA
    cxp1
    3ad2ant1
    oveq2d
    eqtrd
end
