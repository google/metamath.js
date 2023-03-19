include "chil.mm"
include "chod.mm"
include "co.mm"
include "wf.mm"
include "wfn.mm"
include "hosubcli.mm"
include "ffn.mm"
include "ax-mp.mm"

theorem hosubfni
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hoeq.1: |- S : ~H --> ~H
  assume hoeq.2: |- T : ~H --> ~H


  assert |- ( S -op T ) Fn ~H

  proof
    chil
    chil
    cS
    cT
    chod
    co
    #
    wf
    @0
    chil
    wfn
    cS
    cT
    hoeq.1
    hoeq.2
    hosubcli
    chil
    chil
    @0
    ffn
    ax-mp
end
