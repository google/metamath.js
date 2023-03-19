include "wfal.mm"
include "wn.mm"
include "fal.mm"
include "a1i.mm"

theorem fald
  let wth: wff th


  assert |- ( th -> -. F. )

  proof
    wfal
    wn
    wth
    fal
    a1i
end
