include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "chod.mm"
include "co.mm"
include "chot.mm"
include "chos.mm"
include "wceq.mm"
include "wa.mm"
include "hosubcl.mm"
include "honegsub.mm"
include "sylan2.mm"
include "3impb.mm"
include "honegsubdi2.mm"
include "oveq2d.mm"
include "3adant1.mm"
include "eqtr3d.mm"

theorem hosubsub2
  let cS: class S
  let cT: class T
  let cU: class U


  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H /\ U : ~H --> ~H ) -> ( S -op ( T -op U ) ) = ( S +op ( U -op T ) ) )

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
    c1
    cneg
    cT
    cU
    chod
    co
    #
    chot
    co
    #
    chos
    co
    #
    cS
    @3
    chod
    co
    #
    cS
    cU
    cT
    chod
    co
    #
    chos
    co
    #
    @0
    @1
    @2
    @5
    @6
    wceq
    #
    @1
    @2
    wa
    #
    @0
    chil
    chil
    @3
    wf
    @9
    cT
    cU
    hosubcl
    cS
    @3
    honegsub
    sylan2
    3impb
    @1
    @2
    @5
    @8
    wceq
    @0
    @10
    @4
    @7
    cS
    chos
    cT
    cU
    honegsubdi2
    oveq2d
    3adant1
    eqtr3d
end
