include "cv.mm"
include "sseldi.mm"

theorem bnj1213
  let wth: wff th
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bnj1213.1: |- A C_ B
  assume bnj1213.2: |- ( th -> x e. A )


  assert |- ( th -> x e. B )

  proof
    wth
    cA
    cB
    vx
    cv
    bnj1213.1
    bnj1213.2
    sseldi
end
