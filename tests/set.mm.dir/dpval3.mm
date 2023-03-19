include "cdp.mm"
include "co.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "caddc.mm"
include "cdp2.mm"
include "dpval2.mm"
include "df-dp2.mm"
include "eqtr4i.mm"

theorem dpval3
  let cA: class A
  let cB: class B
  assume dpval2.a: |- A e. NN0
  assume dpval2.b: |- B e. RR


  assert |- ( A . B ) = _ A B

  proof
    cA
    cB
    cdp
    co
    cA
    cB
    c1
    cc0
    cdc
    cdiv
    co
    caddc
    co
    cA
    cB
    cdp2
    cA
    cB
    dpval2.a
    dpval2.b
    dpval2
    cA
    cB
    df-dp2
    eqtr4i
end
