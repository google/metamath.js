include "cvv.mm"
include "wcel.mm"
include "wtru.mm"
include "wsbc.mm"
include "wb.mm"
include "sbcg.mm"
include "ax-mp.mm"

theorem sbtru
  let vx: setvar x
  let cA: class A
  assume sbtru.1: |- A e. _V


  assert |- ( [. A / x ]. T. <-> T. )

  proof
    cA
    cvv
    wcel
    wtru
    vx
    cA
    wsbc
    wtru
    wb
    sbtru.1
    wtru
    vx
    cA
    cvv
    sbcg
    ax-mp
end
