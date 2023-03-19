include "csem.mm"
include "wcel.mm"
include "cexid.mm"
include "cin.mm"
include "cmndo.mm"
include "elin.mm"
include "simplbi.mm"
include "df-mndo.mm"
include "eleq2s.mm"

theorem mndoissmgrpOLD
  let cG: class G


  assert |- ( G e. MndOp -> G e. SemiGrp )

  proof
    cG
    csem
    wcel
    #
    cG
    csem
    cexid
    cin
    #
    cmndo
    cG
    @1
    wcel
    @0
    cG
    cexid
    wcel
    cG
    csem
    cexid
    elin
    simplbi
    df-mndo
    eleq2s
end
