include "chil.mm"
include "wf.mm"
include "wa.mm"
include "chod.mm"
include "co.mm"
include "chos.mm"
include "wceq.mm"
include "hosubcl.mm"
include "hosubsub2.mm"
include "3expb.mm"
include "sylan.mm"
include "hosub4.mm"
include "an42s.mm"
include "eqtr4d.mm"

theorem hosubadd4
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U


  assert |- ( ( ( R : ~H --> ~H /\ S : ~H --> ~H ) /\ ( T : ~H --> ~H /\ U : ~H --> ~H ) ) -> ( ( R -op S ) -op ( T -op U ) ) = ( ( R +op U ) -op ( S +op T ) ) )

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
    wa
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
    wa
    #
    wa
    cR
    cS
    chod
    co
    #
    cT
    cU
    chod
    co
    chod
    co
    #
    @6
    cU
    cT
    chod
    co
    chos
    co
    #
    cR
    cU
    chos
    co
    cS
    cT
    chos
    co
    chod
    co
    #
    @2
    chil
    chil
    @6
    wf
    #
    @5
    @7
    @8
    wceq
    #
    cR
    cS
    hosubcl
    @10
    @3
    @4
    @11
    @6
    cT
    cU
    hosubsub2
    3expb
    sylan
    @0
    @4
    @1
    @3
    @9
    @8
    wceq
    cR
    cU
    cS
    cT
    hosub4
    an42s
    eqtr4d
end
