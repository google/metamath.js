include "wo.mm"
include "orc.mm"
include "con3i.mm"

theorem pm2.45
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph \/ ps ) -> -. ph )

  proof
    wph
    wph
    wps
    wo
    wph
    wps
    orc
    con3i
end
