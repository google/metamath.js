include "chl.mm"
include "wcel.mm"
include "ccph.mm"
include "cphl.mm"
include "hlcph.mm"
include "cphphl.mm"
include "syl.mm"

theorem hlphl
  let cW: class W


  assert |- ( W e. CHil -> W e. PreHil )

  proof
    cW
    chl
    wcel
    cW
    ccph
    wcel
    cW
    cphl
    wcel
    cW
    hlcph
    cW
    cphphl
    syl
end
