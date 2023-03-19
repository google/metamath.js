include "wn.mm"
include "pm2.21.mm"
include "com12.mm"

theorem pm2.24
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( -. ph -> ps ) )

  proof
    wph
    wn
    wph
    wps
    wph
    wps
    pm2.21
    com12
end
