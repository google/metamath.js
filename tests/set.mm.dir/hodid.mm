include "chil.mm"
include "wf.mm"
include "chod.mm"
include "co.mm"
include "ch0o.mm"
include "wceq.mm"
include "cif.mm"
include "id.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "ho0f.mm"
include "elimf.mm"
include "hodidi.mm"
include "dedth.mm"

theorem hodid
  let cT: class T


  assert |- ( T : ~H --> ~H -> ( T -op T ) = 0hop )

  proof
    chil
    chil
    cT
    wf
    #
    cT
    cT
    chod
    co
    #
    ch0o
    wceq
    @0
    cT
    ch0o
    cif
    #
    @2
    chod
    co
    #
    ch0o
    wceq
    cT
    ch0o
    cT
    @2
    wceq
    #
    @1
    @3
    ch0o
    @4
    cT
    @2
    cT
    @2
    chod
    @4
    id
    #
    @5
    oveq12d
    eqeq1d
    @2
    chil
    chil
    cT
    ch0o
    ho0f
    elimf
    hodidi
    dedth
end
