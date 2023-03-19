include "cnvc.mm"
include "wcel.mm"
include "cnlm.mm"
include "clmod.mm"
include "nvcnlm.mm"
include "nlmlmod.mm"
include "syl.mm"

theorem nvclmod
  let cW: class W


  assert |- ( W e. NrmVec -> W e. LMod )

  proof
    cW
    cnvc
    wcel
    cW
    cnlm
    wcel
    cW
    clmod
    wcel
    cW
    nvcnlm
    cW
    nlmlmod
    syl
end
