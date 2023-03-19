include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "subsub2.mm"
include "3anidm12.mm"
include "pncan3.mm"
include "eqtrd.mm"

theorem nncan
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A - ( A - B ) ) = B )

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
    cA
    cB
    cmin
    co
    cmin
    co
    #
    cA
    cB
    cA
    cmin
    co
    caddc
    co
    #
    cB
    @0
    @1
    @2
    @3
    wceq
    cA
    cA
    cB
    subsub2
    3anidm12
    cA
    cB
    pncan3
    eqtrd
end
