include "pm2.24i.mm"
include "orri.mm"

theorem orci
  let wph: wff ph
  let wps: wff ps
  assume orci.1: |- ph


  assert |- ( ph \/ ps )

  proof
    wph
    wps
    wph
    wps
    orci.1
    pm2.24i
    orri
end
