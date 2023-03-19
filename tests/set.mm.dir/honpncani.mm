include "chod.mm"
include "co.mm"
include "chos.mm"
include "hosubcli.mm"
include "hoaddsubassi.mm"
include "honpcani.mm"
include "oveq1i.mm"
include "eqtr3i.mm"

theorem honpncani
  let cR: class R
  let cS: class S
  let cT: class T
  assume honpncan.1: |- R : ~H --> ~H
  assume honpncan.2: |- S : ~H --> ~H
  assume honpncan.3: |- T : ~H --> ~H


  assert |- ( ( R -op S ) +op ( S -op T ) ) = ( R -op T )

  proof
    cR
    cS
    chod
    co
    #
    cS
    chos
    co
    #
    cT
    chod
    co
    @0
    cS
    cT
    chod
    co
    chos
    co
    cR
    cT
    chod
    co
    @0
    cS
    cT
    cR
    cS
    honpncan.1
    honpncan.2
    hosubcli
    honpncan.2
    honpncan.3
    hoaddsubassi
    @1
    cR
    cT
    chod
    cR
    cS
    honpncan.1
    honpncan.2
    honpcani
    oveq1i
    eqtr3i
end
