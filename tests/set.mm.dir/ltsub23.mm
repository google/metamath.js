include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "ltsubadd.mm"
include "wb.mm"
include "ltsubadd2.mm"
include "3com23.mm"
include "bitr4d.mm"

theorem ltsub23
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A - B ) < C <-> ( A - C ) < B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    cA
    cB
    cmin
    co
    cC
    clt
    wbr
    cA
    cC
    cB
    caddc
    co
    clt
    wbr
    #
    cA
    cC
    cmin
    co
    cB
    clt
    wbr
    #
    cA
    cB
    cC
    ltsubadd
    @0
    @2
    @1
    @4
    @3
    wb
    cA
    cC
    cB
    ltsubadd2
    3com23
    bitr4d
end
