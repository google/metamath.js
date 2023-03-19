include "wo.mm"
include "olc.mm"
include "con3i.mm"

theorem pm2.46
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph \/ ps ) -> -. ps )

  proof
    wps
    wph
    wps
    wo
    wps
    wph
    olc
    con3i
end
