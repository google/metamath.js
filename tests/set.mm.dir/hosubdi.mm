include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "chot.mm"
include "co.mm"
include "chos.mm"
include "chod.mm"
include "wceq.mm"
include "neg1cn.mm"
include "homulcl.mm"
include "mpan.mm"
include "hoadddi.mm"
include "syl3an3.mm"
include "homul12.mm"
include "mp3an2.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "wa.mm"
include "honegsub.mm"
include "3adant1.mm"
include "syl2an.mm"
include "3impdi.mm"
include "3eqtr3d.mm"

theorem hosubdi
  let cA: class A
  let cT: class T
  let cU: class U


  assert |- ( ( A e. CC /\ T : ~H --> ~H /\ U : ~H --> ~H ) -> ( A .op ( T -op U ) ) = ( ( A .op T ) -op ( A .op U ) ) )

  proof
    cA
    cc
    wcel
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
    cA
    cT
    c1
    cneg
    #
    cU
    chot
    co
    #
    chos
    co
    #
    chot
    co
    #
    cA
    cT
    chot
    co
    #
    @4
    cA
    cU
    chot
    co
    #
    chot
    co
    #
    chos
    co
    #
    cA
    cT
    cU
    chod
    co
    #
    chot
    co
    #
    @8
    @9
    chod
    co
    #
    @3
    @7
    @8
    cA
    @5
    chot
    co
    #
    chos
    co
    #
    @11
    @2
    @0
    @1
    chil
    chil
    @5
    wf
    #
    @7
    @16
    wceq
    @4
    cc
    wcel
    #
    @2
    @17
    neg1cn
    @4
    cU
    homulcl
    mpan
    cA
    cT
    @5
    hoadddi
    syl3an3
    @3
    @15
    @10
    @8
    chos
    @0
    @2
    @15
    @10
    wceq
    #
    @1
    @0
    @18
    @2
    @19
    neg1cn
    cA
    @4
    cU
    homul12
    mp3an2
    3adant2
    oveq2d
    eqtrd
    @1
    @2
    @7
    @13
    wceq
    @0
    @1
    @2
    wa
    @6
    @12
    cA
    chot
    cT
    cU
    honegsub
    oveq2d
    3adant1
    @0
    @1
    @2
    @11
    @14
    wceq
    #
    @0
    @1
    wa
    chil
    chil
    @8
    wf
    chil
    chil
    @9
    wf
    @20
    @0
    @2
    wa
    cA
    cT
    homulcl
    cA
    cU
    homulcl
    @8
    @9
    honegsub
    syl2an
    3impdi
    3eqtr3d
end
