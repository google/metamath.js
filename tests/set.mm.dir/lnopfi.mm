include "clo.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "lnopf.mm"
include "ax-mp.mm"

theorem lnopfi
  let cT: class T
  assume lnopl.1: |- T e. LinOp


  assert |- T : ~H --> ~H

  proof
    cT
    clo
    wcel
    chil
    chil
    cT
    wf
    lnopl.1
    cT
    lnopf
    ax-mp
end
