include "chil.mm"
include "wf.mm"
include "ccom.mm"
include "fco.mm"
include "mp2an.mm"

theorem hocofi
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hoeq.1: |- S : ~H --> ~H
  assume hoeq.2: |- T : ~H --> ~H


  assert |- ( S o. T ) : ~H --> ~H

  proof
    chil
    chil
    cS
    wf
    chil
    chil
    cT
    wf
    chil
    chil
    cS
    cT
    ccom
    wf
    hoeq.1
    hoeq.2
    chil
    chil
    chil
    cS
    cT
    fco
    mp2an
end
