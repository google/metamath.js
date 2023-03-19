include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "ltaddpos.mm"
include "wb.mm"
include "ltsubadd.mm"
include "3anidm13.mm"
include "ancoms.mm"
include "bitr4d.mm"

theorem ltsubpos
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( 0 < A <-> ( B - A ) < B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cc0
    cA
    clt
    wbr
    cB
    cB
    cA
    caddc
    co
    clt
    wbr
    #
    cB
    cA
    cmin
    co
    cB
    clt
    wbr
    #
    cA
    cB
    ltaddpos
    @1
    @0
    @3
    @2
    wb
    #
    @1
    @0
    @4
    cB
    cA
    cB
    ltsubadd
    3anidm13
    ancoms
    bitr4d
end
