include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cedgf.mm"
include "basendxnn.mm"
include "nnrei.mm"
include "baseltedgf.mm"
include "ltneii.mm"

theorem slotsbaseefdif



  assert |- ( Base ` ndx ) =/= ( .ef ` ndx )

  proof
    cnx
    cbs
    cfv
    #
    cnx
    cedgf
    cfv
    @0
    basendxnn
    nnrei
    baseltedgf
    ltneii
end
