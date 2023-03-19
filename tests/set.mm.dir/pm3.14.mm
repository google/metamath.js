include "wa.mm"
include "wn.mm"
include "wo.mm"
include "pm3.1.mm"
include "con2i.mm"

theorem pm3.14
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph \/ -. ps ) -> -. ( ph /\ ps ) )

  proof
    wph
    wps
    wa
    wph
    wn
    wps
    wn
    wo
    wph
    wps
    pm3.1
    con2i
end
