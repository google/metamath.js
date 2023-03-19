include "chos.mm"
include "co.mm"
include "chod.mm"
include "hoaddcomi.mm"
include "oveq1i.mm"
include "hoaddsubassi.mm"
include "hosubcli.mm"
include "3eqtri.mm"

theorem hoaddsubi
  let cR: class R
  let cS: class S
  let cT: class T
  assume hoaddsubass.1: |- R : ~H --> ~H
  assume hoaddsubass.2: |- S : ~H --> ~H
  assume hoaddsubass.3: |- T : ~H --> ~H


  assert |- ( ( R +op S ) -op T ) = ( ( R -op T ) +op S )

  proof
    cR
    cS
    chos
    co
    #
    cT
    chod
    co
    cS
    cR
    chos
    co
    #
    cT
    chod
    co
    cS
    cR
    cT
    chod
    co
    #
    chos
    co
    @2
    cS
    chos
    co
    @0
    @1
    cT
    chod
    cR
    cS
    hoaddsubass.1
    hoaddsubass.2
    hoaddcomi
    oveq1i
    cS
    cR
    cT
    hoaddsubass.2
    hoaddsubass.1
    hoaddsubass.3
    hoaddsubassi
    cS
    @2
    hoaddsubass.2
    cR
    cT
    hoaddsubass.1
    hoaddsubass.3
    hosubcli
    hoaddcomi
    3eqtri
end
