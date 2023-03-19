include "cdc.mm"
include "c9.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "c10.mm"
include "df-dec.mm"
include "9p1e10OLD.mm"
include "oveq1i.mm"
include "eqtri.mm"

theorem dfdecOLD
  let cA: class A
  let cB: class B


  assert |- ; A B = ( ( 10 x. A ) + B )

  proof
    cA
    cB
    cdc
    c9
    c1
    caddc
    co
    #
    cA
    cmul
    co
    #
    cB
    caddc
    co
    c10
    cA
    cmul
    co
    #
    cB
    caddc
    co
    cA
    cB
    df-dec
    @1
    @2
    cB
    caddc
    @0
    c10
    cA
    cmul
    9p1e10OLD
    oveq1i
    oveq1i
    eqtri
end
