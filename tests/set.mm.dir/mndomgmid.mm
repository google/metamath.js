include "cmndo.mm"
include "wcel.mm"
include "cmagm.mm"
include "cexid.mm"
include "mndoismgmOLD.mm"
include "mndoisexid.mm"
include "elind.mm"

theorem mndomgmid
  let cG: class G


  assert |- ( G e. MndOp -> G e. ( Magma i^i ExId ) )

  proof
    cG
    cmndo
    wcel
    cmagm
    cexid
    cG
    cG
    mndoismgmOLD
    cG
    mndoisexid
    elind
end
