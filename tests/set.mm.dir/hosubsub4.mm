include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "chot.mm"
include "co.mm"
include "chod.mm"
include "chos.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "neg1cn.mm"
include "homulcl.mm"
include "mpan.mm"
include "hosubsub.mm"
include "syl3an3.mm"
include "hosubneg.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "hosubcl.mm"
include "honegsub.mm"
include "stoic3.mm"
include "3eqtr3rd.mm"

theorem hosubsub4
  let cS: class S
  let cT: class T
  let cU: class U


  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H /\ U : ~H --> ~H ) -> ( ( S -op T ) -op U ) = ( S -op ( T +op U ) ) )

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
    c1
    cneg
    #
    cU
    chot
    co
    #
    chod
    co
    #
    chod
    co
    #
    cS
    cT
    chod
    co
    #
    @5
    chos
    co
    #
    cS
    cT
    cU
    chos
    co
    #
    chod
    co
    @8
    cU
    chod
    co
    #
    @2
    @0
    @1
    chil
    chil
    @5
    wf
    #
    @7
    @9
    wceq
    @4
    cc
    wcel
    @2
    @12
    neg1cn
    @4
    cU
    homulcl
    mpan
    cS
    cT
    @5
    hosubsub
    syl3an3
    @3
    @6
    @10
    cS
    chod
    @1
    @2
    @6
    @10
    wceq
    @0
    cT
    cU
    hosubneg
    3adant1
    oveq2d
    @0
    @1
    chil
    chil
    @8
    wf
    @2
    @9
    @11
    wceq
    cS
    cT
    hosubcl
    @8
    cU
    honegsub
    stoic3
    3eqtr3rd
end
