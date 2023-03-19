include "cdc.mm"
include "c9.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "df-dec.mm"
include "ovexi.mm"

theorem decex
  let cA: class A
  let cB: class B


  assert |- ; A B e. _V

  proof
    cA
    cB
    cdc
    c9
    c1
    caddc
    co
    cA
    cmul
    co
    cB
    caddc
    cA
    cB
    df-dec
    ovexi
end
