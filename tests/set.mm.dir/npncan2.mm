include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "npncan.mm"
include "3anidm13.mm"
include "subid.mm"
include "adantr.mm"
include "eqtrd.mm"

theorem npncan2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A - B ) + ( B - A ) ) = 0 )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    cA
    cB
    cmin
    co
    cB
    cA
    cmin
    co
    caddc
    co
    #
    cA
    cA
    cmin
    co
    #
    cc0
    @0
    @1
    @2
    @3
    wceq
    cA
    cB
    cA
    npncan
    3anidm13
    @0
    @3
    cc0
    wceq
    @1
    cA
    subid
    adantr
    eqtrd
end
