include "chl.mm"
include "wcel.mm"
include "cbn.mm"
include "ccms.mm"
include "hlbn.mm"
include "bncms.mm"
include "syl.mm"

theorem hlcms
  let cW: class W


  assert |- ( W e. CHil -> W e. CMetSp )

  proof
    cW
    chl
    wcel
    cW
    cbn
    wcel
    cW
    ccms
    wcel
    cW
    hlbn
    cW
    bncms
    syl
end
