include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "rexr.mm"
include "ax-mp.mm"

theorem rexri
  let cA: class A
  assume rexri.1: |- A e. RR


  assert |- A e. RR*

  proof
    cA
    cr
    wcel
    cA
    cxr
    wcel
    rexri.1
    cA
    rexr
    ax-mp
end
