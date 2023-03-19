include "wo.mm"
include "id.mm"
include "pm2.21i.mm"
include "jaoi.mm"
include "mto.mm"

theorem pm3.2ni
  let wph: wff ph
  let wps: wff ps
  assume pm3.2ni.1: |- -. ph
  assume pm3.2ni.2: |- -. ps


  assert |- -. ( ph \/ ps )

  proof
    wph
    wps
    wo
    wph
    pm3.2ni.1
    wph
    wph
    wps
    wph
    id
    wps
    wph
    pm3.2ni.2
    pm2.21i
    jaoi
    mto
end
