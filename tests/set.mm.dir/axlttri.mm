include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cltrr.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "clt.mm"
include "ax-pre-lttri.mm"
include "ltxrlt.mm"
include "wb.mm"
include "ancoms.mm"
include "orbi2d.mm"
include "notbid.mm"
include "3bitr4d.mm"

theorem axlttri
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> -. ( A = B \/ B < A ) ) )

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
    cltrr
    wbr
    cA
    cB
    wceq
    #
    cB
    cA
    cltrr
    wbr
    #
    wo
    #
    wn
    cA
    cB
    clt
    wbr
    @3
    cB
    cA
    clt
    wbr
    #
    wo
    #
    wn
    cA
    cB
    ax-pre-lttri
    cA
    cB
    ltxrlt
    @2
    @7
    @5
    @2
    @6
    @4
    @3
    @1
    @0
    @6
    @4
    wb
    cB
    cA
    ltxrlt
    ancoms
    orbi2d
    notbid
    3bitr4d
end
