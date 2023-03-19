include "wfal.mm"
include "wtru.mm"
include "wn.mm"
include "tru.mm"
include "notnoti.mm"
include "df-fal.mm"
include "mtbir.mm"

theorem fal



  assert |- -. F.

  proof
    wfal
    wtru
    wn
    wtru
    tru
    notnoti
    df-fal
    mtbir
end
