include "cdc.mm"
include "c9.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "cc0.mm"
include "df-dec.mm"
include "9p1e10.mm"
include "oveq1i.mm"
include "eqtri.mm"

theorem dfdec10
  let cA: class A
  let cB: class B


  assert |- ; A B = ( ( ; 1 0 x. A ) + B )

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
    c1
    cc0
    cdc
    #
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
    @3
    cB
    caddc
    @0
    @2
    cA
    cmul
    9p1e10
    oveq1i
    oveq1i
    eqtri
end
