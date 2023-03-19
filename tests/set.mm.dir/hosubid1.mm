include "chil.mm"
include "wf.mm"
include "ch0o.mm"
include "chod.mm"
include "co.mm"
include "chos.mm"
include "wceq.mm"
include "ho0f.mm"
include "ho0sub.mm"
include "mpan2.mm"
include "hodidi.mm"
include "oveq2i.mm"
include "hoaddid1.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem hosubid1
  let cT: class T


  assert |- ( T : ~H --> ~H -> ( T -op 0hop ) = T )

  proof
    chil
    chil
    cT
    wf
    #
    cT
    ch0o
    chod
    co
    #
    cT
    ch0o
    ch0o
    chod
    co
    #
    chos
    co
    #
    cT
    @0
    chil
    chil
    ch0o
    wf
    @1
    @3
    wceq
    ho0f
    cT
    ch0o
    ho0sub
    mpan2
    @0
    @3
    cT
    ch0o
    chos
    co
    cT
    @2
    ch0o
    cT
    chos
    ch0o
    ho0f
    hodidi
    oveq2i
    cT
    hoaddid1
    syl5eq
    eqtrd
end
