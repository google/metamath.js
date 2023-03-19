include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "wceq.mm"
include "wn.mm"
include "wor.mm"
include "wb.mm"
include "ltso.mm"
include "sotrieq.mm"
include "mpan.mm"
include "bicomd.mm"
include "necon1abid.mm"

theorem lttri2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A =/= B <-> ( A < B \/ B < A ) ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    #
    cA
    cB
    clt
    wbr
    cB
    cA
    clt
    wbr
    wo
    #
    cA
    cB
    @0
    cA
    cB
    wceq
    #
    @1
    wn
    #
    cr
    clt
    wor
    @0
    @2
    @3
    wb
    ltso
    cr
    cA
    cB
    clt
    sotrieq
    mpan
    bicomd
    necon1abid
end
