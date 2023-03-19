include "wo.mm"
include "wn.mm"
include "pm2.53.mm"
include "com12.mm"

theorem orel1
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph -> ( ( ph \/ ps ) -> ps ) )

  proof
    wph
    wps
    wo
    wph
    wn
    wps
    wph
    wps
    pm2.53
    com12
end
