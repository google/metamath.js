include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "csle.mm"
include "wbr.mm"
include "cslt.mm"
include "wn.mm"
include "wb.mm"
include "slenlt.mm"
include "ancoms.mm"
include "con2bid.mm"

theorem sltnle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. No /\ B e. No ) -> ( A <s B <-> -. B <_s A ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    wa
    cB
    cA
    csle
    wbr
    #
    cA
    cB
    cslt
    wbr
    #
    @1
    @0
    @2
    @3
    wn
    wb
    cB
    cA
    slenlt
    ancoms
    con2bid
end
