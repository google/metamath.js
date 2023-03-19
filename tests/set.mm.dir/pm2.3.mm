include "wo.mm"
include "pm1.4.mm"
include "orim2i.mm"

theorem pm2.3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ( ps \/ ch ) ) -> ( ph \/ ( ch \/ ps ) ) )

  proof
    wps
    wch
    wo
    wch
    wps
    wo
    wph
    wps
    wch
    pm1.4
    orim2i
end
