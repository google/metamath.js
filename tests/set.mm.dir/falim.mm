include "wfal.mm"
include "fal.mm"
include "pm2.21i.mm"

theorem falim
  let wph: wff ph


  assert |- ( F. -> ph )

  proof
    wfal
    wph
    fal
    pm2.21i
end
