include "wfal.mm"
include "wtru.mm"
include "wn.mm"
include "df-fal.mm"
include "bicomi.mm"

theorem nottru



  assert |- ( -. T. <-> F. )

  proof
    wfal
    wtru
    wn
    df-fal
    bicomi
end
