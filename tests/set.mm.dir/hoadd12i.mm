include "chos.mm"
include "co.mm"
include "hoaddcomi.mm"
include "oveq1i.mm"
include "hoaddassi.mm"
include "3eqtr3i.mm"

theorem hoadd12i
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hods.1: |- R : ~H --> ~H
  assume hods.2: |- S : ~H --> ~H
  assume hods.3: |- T : ~H --> ~H


  assert |- ( R +op ( S +op T ) ) = ( S +op ( R +op T ) )

  proof
    cR
    cS
    chos
    co
    #
    cT
    chos
    co
    cS
    cR
    chos
    co
    #
    cT
    chos
    co
    cR
    cS
    cT
    chos
    co
    chos
    co
    cS
    cR
    cT
    chos
    co
    chos
    co
    @0
    @1
    cT
    chos
    cR
    cS
    hods.1
    hods.2
    hoaddcomi
    oveq1i
    cR
    cS
    cT
    hods.1
    hods.2
    hods.3
    hoaddassi
    cS
    cR
    cT
    hods.2
    hods.1
    hods.3
    hoaddassi
    3eqtr3i
end
