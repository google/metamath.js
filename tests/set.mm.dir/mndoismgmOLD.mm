include "cmndo.mm"
include "wcel.mm"
include "csem.mm"
include "cmagm.mm"
include "mndoissmgrpOLD.mm"
include "smgrpismgmOLD.mm"
include "syl.mm"

theorem mndoismgmOLD
  let cG: class G


  assert |- ( G e. MndOp -> G e. Magma )

  proof
    cG
    cmndo
    wcel
    cG
    csem
    wcel
    cG
    cmagm
    wcel
    cG
    mndoissmgrpOLD
    cG
    smgrpismgmOLD
    syl
end
