include "pm2.67-2.mm"

theorem pm2.67
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph \/ ps ) -> ps ) -> ( ph -> ps ) )

  proof
    wph
    wps
    wps
    pm2.67-2
end
