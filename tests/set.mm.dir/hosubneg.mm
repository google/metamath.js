include "chil.mm"
include "wf.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "chot.mm"
include "co.mm"
include "chos.mm"
include "chod.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "neg1cn.mm"
include "homulcl.mm"
include "mpan.mm"
include "honegsub.mm"
include "sylan2.mm"
include "honegneg.mm"
include "oveq2d.mm"
include "adantl.mm"
include "eqtr3d.mm"

theorem hosubneg
  let cT: class T
  let cU: class U


  assert |- ( ( T : ~H --> ~H /\ U : ~H --> ~H ) -> ( T -op ( -u 1 .op U ) ) = ( T +op U ) )

  proof
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
    cT
    c1
    cneg
    #
    @2
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
    cT
    @3
    chod
    co
    #
    cT
    cU
    chos
    co
    #
    @1
    @0
    chil
    chil
    @3
    wf
    #
    @5
    @6
    wceq
    @2
    cc
    wcel
    @1
    @8
    neg1cn
    @2
    cU
    homulcl
    mpan
    cT
    @3
    honegsub
    sylan2
    @1
    @5
    @7
    wceq
    @0
    @1
    @4
    cU
    cT
    chos
    cU
    honegneg
    oveq2d
    adantl
    eqtr3d
end
