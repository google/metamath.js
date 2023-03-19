include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "crp.mm"
include "posdif.mm"
include "wb.mm"
include "resubcl.mm"
include "ancoms.mm"
include "elrp.mm"
include "baib.mm"
include "syl.mm"
include "bitr4d.mm"

theorem difrp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> ( B - A ) e. RR+ ) )

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
    #
    cA
    cB
    clt
    wbr
    cc0
    cB
    cA
    cmin
    co
    #
    clt
    wbr
    #
    @3
    crp
    wcel
    #
    cA
    cB
    posdif
    @2
    @3
    cr
    wcel
    #
    @5
    @4
    wb
    @1
    @0
    @6
    cB
    cA
    resubcl
    ancoms
    @5
    @6
    @4
    @3
    elrp
    baib
    syl
    bitr4d
end
