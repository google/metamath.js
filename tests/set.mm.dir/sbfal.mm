include "cvv.mm"
include "wcel.mm"
include "wfal.mm"
include "wsbc.mm"
include "wb.mm"
include "sbcg.mm"
include "ax-mp.mm"

theorem sbfal
  let vx: setvar x
  let cA: class A
  assume sbfal.1: |- A e. _V


  assert |- ( [. A / x ]. F. <-> F. )

  proof
    cA
    cvv
    wcel
    wfal
    vx
    cA
    wsbc
    wfal
    wb
    sbfal.1
    wfal
    vx
    cA
    cvv
    sbcg
    ax-mp
end
