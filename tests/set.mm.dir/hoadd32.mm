include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "chos.mm"
include "co.mm"
include "wceq.mm"
include "hoaddcom.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "hoaddass.mm"
include "3com23.mm"
include "3eqtr4d.mm"

theorem hoadd32
  let cR: class R
  let cS: class S
  let cT: class T


  assert |- ( ( R : ~H --> ~H /\ S : ~H --> ~H /\ T : ~H --> ~H ) -> ( ( R +op S ) +op T ) = ( ( R +op T ) +op S ) )

  proof
    chil
    chil
    cR
    wf
    #
    chil
    chil
    cS
    wf
    #
    chil
    chil
    cT
    wf
    #
    w3a
    #
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
    #
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
    #
    @3
    @4
    @5
    cR
    chos
    @1
    @2
    @4
    @5
    wceq
    @0
    cS
    cT
    hoaddcom
    3adant1
    oveq2d
    cR
    cS
    cT
    hoaddass
    @0
    @2
    @1
    @7
    @6
    wceq
    cR
    cT
    cS
    hoaddass
    3com23
    3eqtr4d
end
