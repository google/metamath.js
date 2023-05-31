include "pm2.24.mm"
include "orrd.mm"

theorem orc
  param wph: wff ph
  param wps: wff ps


  assert |- ( ph -> ( ph \/ ps ) )

  proof
    wph
    wph
    wps
    wph
    wps
    pm2.24
    orrd
end
