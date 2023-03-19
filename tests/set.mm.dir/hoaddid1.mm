include "chil.mm"
include "wf.mm"
include "ch0o.mm"
include "chos.mm"
include "co.mm"
include "wceq.mm"
include "cif.mm"
include "oveq1.mm"
include "id.mm"
include "eqeq12d.mm"
include "ho0f.mm"
include "elimf.mm"
include "hoaddid1i.mm"
include "dedth.mm"

theorem hoaddid1
  let cT: class T


  assert |- ( T : ~H --> ~H -> ( T +op 0hop ) = T )

  proof
    chil
    chil
    cT
    wf
    #
    cT
    ch0o
    chos
    co
    #
    cT
    wceq
    @0
    cT
    ch0o
    cif
    #
    ch0o
    chos
    co
    #
    @2
    wceq
    cT
    ch0o
    cT
    @2
    wceq
    #
    @1
    @3
    cT
    @2
    cT
    @2
    ch0o
    chos
    oveq1
    @4
    id
    eqeq12d
    @2
    chil
    chil
    cT
    ch0o
    ho0f
    elimf
    hoaddid1i
    dedth
end
