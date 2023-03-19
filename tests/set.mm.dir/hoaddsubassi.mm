include "chil.mm"
include "wf.mm"
include "chos.mm"
include "co.mm"
include "chod.mm"
include "wceq.mm"
include "hoaddsubass.mm"
include "mp3an.mm"

theorem hoaddsubassi
  let cR: class R
  let cS: class S
  let cT: class T
  assume hoaddsubass.1: |- R : ~H --> ~H
  assume hoaddsubass.2: |- S : ~H --> ~H
  assume hoaddsubass.3: |- T : ~H --> ~H


  assert |- ( ( R +op S ) -op T ) = ( R +op ( S -op T ) )

  proof
    chil
    chil
    cR
    wf
    chil
    chil
    cS
    wf
    chil
    chil
    cT
    wf
    cR
    cS
    chos
    co
    cT
    chod
    co
    cR
    cS
    cT
    chod
    co
    chos
    co
    wceq
    hoaddsubass.1
    hoaddsubass.2
    hoaddsubass.3
    cR
    cS
    cT
    hoaddsubass
    mp3an
end
