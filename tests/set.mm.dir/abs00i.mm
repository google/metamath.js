include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "abs00.mm"
include "ax-mp.mm"

theorem abs00i
  let cA: class A
  assume absvalsqi.1: |- A e. CC


  assert |- ( ( abs ` A ) = 0 <-> A = 0 )

  proof
    cA
    cc
    wcel
    cA
    cabs
    cfv
    cc0
    wceq
    cA
    cc0
    wceq
    wb
    absvalsqi.1
    cA
    abs00
    ax-mp
end
