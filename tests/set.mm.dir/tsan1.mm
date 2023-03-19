include "wn.mm"
include "wo.mm"
include "wa.mm"
include "pm3.12.mm"
include "a1i.mm"

theorem tsan1
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ( -. ph \/ -. ps ) \/ ( ph /\ ps ) ) )

  proof
    wph
    wn
    wps
    wn
    wo
    wph
    wps
    wa
    wo
    wth
    wph
    wps
    pm3.12
    a1i
end
