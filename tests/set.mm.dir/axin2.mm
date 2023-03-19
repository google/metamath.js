include "pm2.21.mm"

theorem axin2
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph -> ( ph -> ps ) )

  proof
    wph
    wps
    pm2.21
end
