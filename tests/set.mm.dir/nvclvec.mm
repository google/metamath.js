include "cnvc.mm"
include "wcel.mm"
include "cnlm.mm"
include "clvec.mm"
include "isnvc.mm"
include "simprbi.mm"

theorem nvclvec
  let cW: class W


  assert |- ( W e. NrmVec -> W e. LVec )

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
    simprbi
end
