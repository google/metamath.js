include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "chos.mm"
include "co.mm"
include "chod.mm"
include "wceq.mm"
include "wa.mm"
include "hoaddcom.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "hoaddsubass.mm"
include "3com12.mm"
include "wi.mm"
include "hosubcl.mm"
include "ex.mm"
include "syl5.mm"
include "expd.mm"
include "com12.mm"
include "3imp.mm"
include "3eqtrd.mm"

theorem hoaddsub
  let cS: class S
  let cT: class T
  let cU: class U


  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H /\ U : ~H --> ~H ) -> ( ( S +op T ) -op U ) = ( ( S -op U ) +op T ) )

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
    chos
    co
    #
    cU
    chod
    co
    #
    cT
    cS
    chos
    co
    #
    cU
    chod
    co
    #
    cT
    cS
    cU
    chod
    co
    #
    chos
    co
    #
    @7
    cT
    chos
    co
    #
    @0
    @1
    @4
    @6
    wceq
    @2
    @0
    @1
    wa
    @3
    @5
    cU
    chod
    cS
    cT
    hoaddcom
    oveq1d
    3adant3
    @1
    @0
    @2
    @6
    @8
    wceq
    cT
    cS
    cU
    hoaddsubass
    3com12
    @0
    @1
    @2
    @8
    @9
    wceq
    #
    @1
    @0
    @2
    @10
    wi
    @1
    @0
    @2
    @10
    @0
    @2
    wa
    chil
    chil
    @7
    wf
    #
    @1
    @10
    cS
    cU
    hosubcl
    @1
    @11
    @10
    cT
    @7
    hoaddcom
    ex
    syl5
    expd
    com12
    3imp
    3eqtrd
end
