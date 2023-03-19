include "cfne.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wex.mm"
include "fnetg.mm"
include "sselda.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "eltg3.mm"
include "syl.mm"
include "ibi.mm"

theorem fneuni
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S

  disjoint A x
  disjoint B x
  disjoint S x
  assert |- ( ( A Fne B /\ S e. A ) -> E. x ( x C_ B /\ S = U. x ) )

  proof
    cA
    cB
    cfne
    wbr
    #
    cS
    cA
    wcel
    wa
    cS
    cB
    ctg
    cfv
    #
    wcel
    #
    vx
    cv
    #
    cB
    wss
    cS
    @3
    cuni
    wceq
    wa
    vx
    wex
    #
    @0
    cA
    @1
    cS
    cA
    cB
    fnetg
    sselda
    @2
    @4
    @2
    cB
    ctg
    cdm
    #
    wcel
    @2
    @4
    wb
    cS
    cB
    ctg
    elfvdm
    vx
    cS
    cB
    @5
    eltg3
    syl
    ibi
    syl
end
