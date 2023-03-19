include "cid.mm"
include "chil.mm"
include "cres.mm"
include "cuo.mm"
include "wcel.mm"
include "clo.mm"
include "idunop.mm"
include "unoplin.mm"
include "ax-mp.mm"

theorem idlnop



  assert |- ( _I |` ~H ) e. LinOp

  proof
    cid
    chil
    cres
    #
    cuo
    wcel
    @0
    clo
    wcel
    idunop
    @0
    unoplin
    ax-mp
end
