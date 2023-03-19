include "wfal.mm"
include "wn.mm"
include "fal.mm"
include "pm2.24i.mm"

theorem negsym1
  let wph: wff ph


  assert |- ( -. -. F. -> -. ph )

  proof
    wfal
    wn
    wph
    wn
    fal
    pm2.24i
end
