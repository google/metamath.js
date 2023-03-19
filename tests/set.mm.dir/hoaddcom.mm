include "chil.mm"
include "wf.mm"
include "chos.mm"
include "co.mm"
include "wceq.mm"
include "ch0o.mm"
include "cif.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "ho0f.mm"
include "elimf.mm"
include "hoaddcomi.mm"
include "dedth2h.mm"

theorem hoaddcom
  let cS: class S
  let cT: class T


  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H ) -> ( S +op T ) = ( T +op S ) )

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
    cS
    cT
    chos
    co
    #
    cT
    cS
    chos
    co
    #
    wceq
    @0
    cS
    ch0o
    cif
    #
    cT
    chos
    co
    #
    cT
    @4
    chos
    co
    #
    wceq
    @4
    @1
    cT
    ch0o
    cif
    #
    chos
    co
    #
    @7
    @4
    chos
    co
    #
    wceq
    cS
    cT
    ch0o
    ch0o
    cS
    @4
    wceq
    @2
    @5
    @3
    @6
    cS
    @4
    cT
    chos
    oveq1
    cS
    @4
    cT
    chos
    oveq2
    eqeq12d
    cT
    @7
    wceq
    @5
    @8
    @6
    @9
    cT
    @7
    @4
    chos
    oveq2
    cT
    @7
    @4
    chos
    oveq1
    eqeq12d
    @4
    @7
    chil
    chil
    cS
    ch0o
    ho0f
    elimf
    chil
    chil
    cT
    ch0o
    ho0f
    elimf
    hoaddcomi
    dedth2h
end
