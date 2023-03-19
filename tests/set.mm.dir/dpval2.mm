include "cdp.mm"
include "co.mm"
include "cdp2.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "caddc.mm"
include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "wceq.mm"
include "dpval.mm"
include "mp2an.mm"
include "df-dp2.mm"
include "eqtri.mm"

theorem dpval2
  let cA: class A
  let cB: class B
  assume dpval2.a: |- A e. NN0
  assume dpval2.b: |- B e. RR


  assert |- ( A . B ) = ( A + ( B / ; 1 0 ) )

  proof
    cA
    cB
    cdp
    co
    #
    cA
    cB
    cdp2
    #
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
    cn0
    wcel
    cB
    cr
    wcel
    @0
    @1
    wceq
    dpval2.a
    dpval2.b
    cA
    cB
    dpval
    mp2an
    cA
    cB
    df-dp2
    eqtri
end
