include "cnvc.mm"
include "wcel.mm"
include "cnlm.mm"
include "clvec.mm"
include "isnvc.mm"
include "simplbi.mm"

theorem nvcnlm
  let cW: class W


  assert |- ( W e. NrmVec -> W e. NrmMod )

  proof
    cW
    cnvc
    wcel
    cW
    cnlm
    wcel
    cW
    clvec
    wcel
    cW
    isnvc
    simplbi
end
