include "chil.mm"
include "wf.mm"
include "c1.mm"
include "cneg.mm"
include "chot.mm"
include "co.mm"
include "chos.mm"
include "chod.mm"
include "wceq.mm"
include "ch0o.mm"
include "cif.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ho0f.mm"
include "elimf.mm"
include "honegsubi.mm"
include "dedth2h.mm"

theorem honegsub
  let cT: class T
  let cU: class U


  assert |- ( ( T : ~H --> ~H /\ U : ~H --> ~H ) -> ( T +op ( -u 1 .op U ) ) = ( T -op U ) )

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
    cT
    cU
    chod
    co
    #
    wceq
    @0
    cT
    ch0o
    cif
    #
    @3
    chos
    co
    #
    @6
    cU
    chod
    co
    #
    wceq
    @6
    @2
    @1
    cU
    ch0o
    cif
    #
    chot
    co
    #
    chos
    co
    #
    @6
    @9
    chod
    co
    #
    wceq
    cT
    cU
    ch0o
    ch0o
    cT
    @6
    wceq
    @4
    @7
    @5
    @8
    cT
    @6
    @3
    chos
    oveq1
    cT
    @6
    cU
    chod
    oveq1
    eqeq12d
    cU
    @9
    wceq
    #
    @7
    @11
    @8
    @12
    @13
    @3
    @10
    @6
    chos
    cU
    @9
    @2
    chot
    oveq2
    oveq2d
    cU
    @9
    @6
    chod
    oveq2
    eqeq12d
    @6
    @9
    chil
    chil
    cT
    ch0o
    ho0f
    elimf
    chil
    chil
    cU
    ch0o
    ho0f
    elimf
    honegsubi
    dedth2h
end
