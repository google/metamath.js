include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "chod.mm"
include "co.mm"
include "chos.mm"
include "hosubsub2.mm"
include "wceq.mm"
include "hoaddsubass.mm"
include "hoaddsub.mm"
include "eqtr3d.mm"
include "3com23.mm"
include "eqtrd.mm"

theorem hosubsub
  let cS: class S
  let cT: class T
  let cU: class U


  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H /\ U : ~H --> ~H ) -> ( S -op ( T -op U ) ) = ( ( S -op T ) +op U ) )

  proof
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
    chil
    chil
    cU
    wf
    #
    w3a
    cS
    cT
    cU
    chod
    co
    chod
    co
    cS
    cU
    cT
    chod
    co
    chos
    co
    #
    cS
    cT
    chod
    co
    cU
    chos
    co
    #
    cS
    cT
    cU
    hosubsub2
    @0
    @2
    @1
    @3
    @4
    wceq
    @0
    @2
    @1
    w3a
    cS
    cU
    chos
    co
    cT
    chod
    co
    @3
    @4
    cS
    cU
    cT
    hoaddsubass
    cS
    cU
    cT
    hoaddsub
    eqtr3d
    3com23
    eqtrd
end
