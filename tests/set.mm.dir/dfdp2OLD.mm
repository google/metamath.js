include "cdp2.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "c10.mm"
include "df-dp2.mm"
include "dec10OLD.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "eqtri.mm"

theorem dfdp2OLD
  let cA: class A
  let cB: class B


  assert |- _ A B = ( A + ( B / 10 ) )

  proof
    cA
    cB
    cdp2
    cA
    cB
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    caddc
    co
    cA
    cB
    c10
    cdiv
    co
    #
    caddc
    co
    cA
    cB
    df-dp2
    @1
    @2
    cA
    caddc
    @0
    c10
    cB
    cdiv
    c10
    @0
    dec10OLD
    eqcomi
    oveq2i
    oveq2i
    eqtri
end
