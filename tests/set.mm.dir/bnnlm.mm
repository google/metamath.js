include "cbn.mm"
include "wcel.mm"
include "cnvc.mm"
include "cnlm.mm"
include "bnnvc.mm"
include "nvcnlm.mm"
include "syl.mm"

theorem bnnlm
  let cW: class W


  assert |- ( W e. Ban -> W e. NrmMod )

  proof
    cW
    cbn
    wcel
    cW
    cnvc
    wcel
    cW
    cnlm
    wcel
    cW
    bnnvc
    cW
    nvcnlm
    syl
end
