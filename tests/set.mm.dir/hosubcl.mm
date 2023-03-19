include "chil.mm"
include "wf.mm"
include "chod.mm"
include "co.mm"
include "ch0o.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "feq1d.mm"
include "oveq2.mm"
include "ho0f.mm"
include "elimf.mm"
include "hosubcli.mm"
include "dedth2h.mm"

theorem hosubcl
  let cS: class S
  let cT: class T


  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H ) -> ( S -op T ) : ~H --> ~H )

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
    cS
    cT
    chod
    co
    #
    wf
    chil
    chil
    @0
    cS
    ch0o
    cif
    #
    cT
    chod
    co
    #
    wf
    chil
    chil
    @3
    @1
    cT
    ch0o
    cif
    #
    chod
    co
    #
    wf
    cS
    cT
    ch0o
    ch0o
    cS
    @3
    wceq
    chil
    chil
    @2
    @4
    cS
    @3
    cT
    chod
    oveq1
    feq1d
    cT
    @5
    wceq
    chil
    chil
    @4
    @6
    cT
    @5
    @3
    chod
    oveq2
    feq1d
    @3
    @5
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
    hosubcli
    dedth2h
end
