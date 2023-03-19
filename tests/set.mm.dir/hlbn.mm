include "chl.mm"
include "wcel.mm"
include "cbn.mm"
include "ccph.mm"
include "ishl.mm"
include "simplbi.mm"

theorem hlbn
  let cW: class W


  assert |- ( W e. CHil -> W e. Ban )

  proof
    cW
    chl
    wcel
    cW
    cbn
    wcel
    cW
    ccph
    wcel
    cW
    ishl
    simplbi
end
