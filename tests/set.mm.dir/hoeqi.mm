include "chil.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wb.mm"
include "hoeq.mm"
include "mp2an.mm"

theorem hoeqi
  let vx: setvar x
  let cS: class S
  let cT: class T
  assume hoeq.1: |- S : ~H --> ~H
  assume hoeq.2: |- T : ~H --> ~H

  disjoint S x
  disjoint T x
  assert |- ( A. x e. ~H ( S ` x ) = ( T ` x ) <-> S = T )

  proof
    chil
    chil
    cS
    wf
    chil
    chil
    cT
    wf
    vx
    cv
    #
    cS
    cfv
    @0
    cT
    cfv
    wceq
    vx
    chil
    wral
    cS
    cT
    wceq
    wb
    hoeq.1
    hoeq.2
    vx
    cS
    cT
    hoeq
    mp2an
end
