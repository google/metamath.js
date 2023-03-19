include "wo.mm"
include "wn.mm"
include "pm2.46.mm"
include "olcd.mm"

theorem pm2.49
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph \/ ps ) -> ( -. ph \/ -. ps ) )

  proof
    wph
    wps
    wo
    wn
    wps
    wn
    wph
    wn
    wph
    wps
    pm2.46
    olcd
end
