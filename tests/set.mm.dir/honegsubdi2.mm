include "chil.mm"
include "wf.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "chod.mm"
include "co.mm"
include "chot.mm"
include "chos.mm"
include "honegsubdi.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "neg1cn.mm"
include "homulcl.mm"
include "mpan.mm"
include "hoaddcom.mm"
include "sylan.mm"
include "honegsub.mm"
include "ancoms.mm"
include "3eqtrd.mm"

theorem honegsubdi2
  let cT: class T
  let cU: class U


  assert |- ( ( T : ~H --> ~H /\ U : ~H --> ~H ) -> ( -u 1 .op ( T -op U ) ) = ( U -op T ) )

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
    c1
    cneg
    #
    cT
    cU
    chod
    co
    chot
    co
    @2
    cT
    chot
    co
    #
    cU
    chos
    co
    #
    cU
    @3
    chos
    co
    #
    cU
    cT
    chod
    co
    #
    cT
    cU
    honegsubdi
    @0
    chil
    chil
    @3
    wf
    #
    @1
    @4
    @5
    wceq
    @2
    cc
    wcel
    @0
    @7
    neg1cn
    @2
    cT
    homulcl
    mpan
    @3
    cU
    hoaddcom
    sylan
    @1
    @0
    @5
    @6
    wceq
    cU
    cT
    honegsub
    ancoms
    3eqtrd
end
