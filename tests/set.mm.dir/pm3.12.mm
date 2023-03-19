include "wn.mm"
include "wo.mm"
include "wa.mm"
include "pm3.11.mm"
include "orri.mm"

theorem pm3.12
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph \/ -. ps ) \/ ( ph /\ ps ) )

  proof
    wph
    wn
    wps
    wn
    wo
    wph
    wps
    wa
    wph
    wps
    pm3.11
    orri
end
