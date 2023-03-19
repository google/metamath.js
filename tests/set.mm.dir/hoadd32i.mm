include "chos.mm"
include "co.mm"
include "hoaddcomi.mm"
include "oveq2i.mm"
include "hoaddassi.mm"
include "3eqtr4i.mm"

theorem hoadd32i
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hods.1: |- R : ~H --> ~H
  assume hods.2: |- S : ~H --> ~H
  assume hods.3: |- T : ~H --> ~H


  assert |- ( ( R +op S ) +op T ) = ( ( R +op T ) +op S )

  proof
    cR
    cS
    cT
    chos
    co
    #
    chos
    co
    cR
    cT
    cS
    chos
    co
    #
    chos
    co
    cR
    cS
    chos
    co
    cT
    chos
    co
    cR
    cT
    chos
    co
    cS
    chos
    co
    @0
    @1
    cR
    chos
    cS
    cT
    hods.2
    hods.3
    hoaddcomi
    oveq2i
    cR
    cS
    cT
    hods.1
    hods.2
    hods.3
    hoaddassi
    cR
    cT
    cS
    hods.1
    hods.3
    hods.2
    hoaddassi
    3eqtr4i
end
