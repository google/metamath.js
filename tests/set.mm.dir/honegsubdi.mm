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
include "honegdi.mm"
include "sylan2.mm"
include "honegsub.mm"
include "oveq2d.mm"
include "honegneg.mm"
include "adantl.mm"
include "3eqtr3d.mm"

theorem honegsubdi
  let cT: class T
  let cU: class U


  assert |- ( ( T : ~H --> ~H /\ U : ~H --> ~H ) -> ( -u 1 .op ( T -op U ) ) = ( ( -u 1 .op T ) +op U ) )

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
    #
    c1
    cneg
    #
    cT
    @3
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
    @3
    cT
    chot
    co
    #
    @3
    @4
    chot
    co
    #
    chos
    co
    #
    @3
    cT
    cU
    chod
    co
    #
    chot
    co
    @7
    cU
    chos
    co
    @1
    @0
    chil
    chil
    @4
    wf
    #
    @6
    @9
    wceq
    @3
    cc
    wcel
    @1
    @11
    neg1cn
    @3
    cU
    homulcl
    mpan
    cT
    @4
    honegdi
    sylan2
    @2
    @5
    @10
    @3
    chot
    cT
    cU
    honegsub
    oveq2d
    @2
    @8
    cU
    @7
    chos
    @1
    @8
    cU
    wceq
    @0
    cU
    honegneg
    adantl
    oveq2d
    3eqtr3d
end
