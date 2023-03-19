include "chil.mm"
include "wf.mm"
include "chos.mm"
include "co.mm"
include "hoaddcl.mm"
include "mp2an.mm"

theorem hoaddcli
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hoeq.1: |- S : ~H --> ~H
  assume hoeq.2: |- T : ~H --> ~H


  assert |- ( S +op T ) : ~H --> ~H

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
    chos
    co
    wf
    hoeq.1
    hoeq.2
    cS
    cT
    hoaddcl
    mp2an
end
