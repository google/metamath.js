include "chil.mm"
include "wf.mm"
include "chio.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "dfiop2.mm"
include "coeq2i.mm"
include "fcoi1.mm"
include "syl5eq.mm"

theorem hoico1
  let cT: class T


  assert |- ( T : ~H --> ~H -> ( T o. Iop ) = T )

  proof
    chil
    chil
    cT
    wf
    cT
    chio
    ccom
    cT
    cid
    chil
    cres
    #
    ccom
    cT
    chio
    @0
    cT
    dfiop2
    coeq2i
    chil
    chil
    cT
    fcoi1
    syl5eq
end
