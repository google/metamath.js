include "chil.mm"
include "ccom.mm"
include "wf.mm"
include "wfn.mm"
include "hocofi.mm"
include "ffn.mm"
include "ax-mp.mm"

theorem hocofni
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hoeq.1: |- S : ~H --> ~H
  assume hoeq.2: |- T : ~H --> ~H


  assert |- ( S o. T ) Fn ~H

  proof
    chil
    chil
    cS
    cT
    ccom
    #
    wf
    @0
    chil
    wfn
    cS
    cT
    hoeq.1
    hoeq.2
    hocofi
    chil
    chil
    @0
    ffn
    ax-mp
end
