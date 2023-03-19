include "cdc.mm"
include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cvv.mm"
include "dfdecOLD.mm"
include "ovex.mm"
include "eqeltri.mm"

theorem decexOLD
  let cA: class A
  let cB: class B


  assert |- ; A B e. _V

  proof
    cA
    cB
    cdc
    c10
    cA
    cmul
    co
    #
    cB
    caddc
    co
    cvv
    cA
    cB
    dfdecOLD
    @0
    cB
    caddc
    ovex
    eqeltri
end
