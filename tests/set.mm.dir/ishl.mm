include "cbn.mm"
include "ccph.mm"
include "chl.mm"
include "df-hl.mm"
include "elin2.mm"

theorem ishl
  let cW: class W


  assert |- ( W e. CHil <-> ( W e. Ban /\ W e. CPreHil ) )

  proof
    cW
    cbn
    ccph
    chl
    df-hl
    elin2
end
