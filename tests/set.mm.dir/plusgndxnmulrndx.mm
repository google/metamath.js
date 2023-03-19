include "cnx.mm"
include "cplusg.mm"
include "cfv.mm"
include "c2.mm"
include "cmulr.mm"
include "plusgndx.mm"
include "c3.mm"
include "2re.mm"
include "2lt3.mm"
include "ltneii.mm"
include "mulrndx.mm"
include "neeqtrri.mm"
include "eqnetri.mm"

theorem plusgndxnmulrndx



  assert |- ( +g ` ndx ) =/= ( .r ` ndx )

  proof
    cnx
    cplusg
    cfv
    c2
    cnx
    cmulr
    cfv
    #
    plusgndx
    c2
    c3
    @0
    c2
    c3
    2re
    2lt3
    ltneii
    mulrndx
    neeqtrri
    eqnetri
end
