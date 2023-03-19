include "chil.mm"
include "wf.mm"
include "chio.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "dfiop2.mm"
include "coeq1i.mm"
include "fcoi2.mm"
include "syl5eq.mm"

theorem hoico2
  let cT: class T


  assert |- ( T : ~H --> ~H -> ( Iop o. T ) = T )

  proof
    chil
    chil
    cT
    wf
    chio
    cT
    ccom
    cid
    chil
    cres
    #
    cT
    ccom
    cT
    chio
    @0
    cT
    dfiop2
    coeq1i
    chil
    chil
    cT
    fcoi2
    syl5eq
end
