include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "chos.mm"
include "co.mm"
include "ch0o.mm"
include "chod.mm"
include "wceq.mm"
include "ho0f.mm"
include "hosubcl.mm"
include "mpan.mm"
include "hoaddass.mm"
include "syl3an3.mm"
include "hoaddcl.mm"
include "ho0sub.mm"
include "stoic3.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem hoaddsubass
  let cS: class S
  let cT: class T
  let cU: class U


  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H /\ U : ~H --> ~H ) -> ( ( S +op T ) -op U ) = ( S +op ( T -op U ) ) )

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
    #
    cS
    cT
    chos
    co
    #
    ch0o
    cU
    chod
    co
    #
    chos
    co
    #
    cS
    cT
    @5
    chos
    co
    #
    chos
    co
    #
    @4
    cU
    chod
    co
    #
    cS
    cT
    cU
    chod
    co
    #
    chos
    co
    @2
    @0
    @1
    chil
    chil
    @5
    wf
    #
    @6
    @8
    wceq
    chil
    chil
    ch0o
    wf
    @2
    @11
    ho0f
    ch0o
    cU
    hosubcl
    mpan
    cS
    cT
    @5
    hoaddass
    syl3an3
    @0
    @1
    chil
    chil
    @4
    wf
    @2
    @9
    @6
    wceq
    cS
    cT
    hoaddcl
    @4
    cU
    ho0sub
    stoic3
    @3
    @10
    @7
    cS
    chos
    @1
    @2
    @10
    @7
    wceq
    @0
    cT
    cU
    ho0sub
    3adant1
    oveq2d
    3eqtr4d
end
