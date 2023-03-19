include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "cmv.mm"
include "wceq.mm"
include "hvaddsubass.mm"
include "3anidm13.mm"
include "hvpncan2.mm"
include "eqtr3d.mm"

theorem hvpncan3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A +h ( B -h A ) ) = B )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    cA
    cB
    cva
    co
    cA
    cmv
    co
    #
    cA
    cB
    cA
    cmv
    co
    cva
    co
    #
    cB
    @0
    @1
    @2
    @3
    wceq
    cA
    cB
    cA
    hvaddsubass
    3anidm13
    cA
    cB
    hvpncan2
    eqtr3d
end
