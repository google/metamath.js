include "wo.mm"
include "wn.mm"
include "pm2.45.mm"
include "orcd.mm"

theorem pm2.47
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph \/ ps ) -> ( -. ph \/ ps ) )

  proof
    wph
    wps
    wo
    wn
    wph
    wn
    wps
    wph
    wps
    pm2.45
    orcd
end
