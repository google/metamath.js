include "chil.mm"
include "chos.mm"
include "co.mm"
include "wf.mm"
include "wfn.mm"
include "hoaddcli.mm"
include "ffn.mm"
include "ax-mp.mm"

theorem hoaddfni
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hoeq.1: |- S : ~H --> ~H
  assume hoeq.2: |- T : ~H --> ~H


  assert |- ( S +op T ) Fn ~H

  proof
    chil
    chil
    cS
    cT
    chos
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
    hoaddcli
    chil
    chil
    @0
    ffn
    ax-mp
end
