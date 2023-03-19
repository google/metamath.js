include "wi.mm"
include "jarl.mm"
include "orrd.mm"

theorem pm2.68
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -> ps ) -> ps ) -> ( ph \/ ps ) )

  proof
    wph
    wps
    wi
    wps
    wi
    wph
    wps
    wph
    wps
    wps
    jarl
    orrd
end
