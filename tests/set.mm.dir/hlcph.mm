include "chl.mm"
include "wcel.mm"
include "cbn.mm"
include "ccph.mm"
include "ishl.mm"
include "simprbi.mm"

theorem hlcph
  let cW: class W


  assert |- ( W e. CHil -> W e. CPreHil )

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
    simprbi
end
