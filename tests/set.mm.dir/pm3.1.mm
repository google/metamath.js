include "wa.mm"
include "wn.mm"
include "wo.mm"
include "anor.mm"
include "biimpi.mm"

theorem pm3.1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ps ) -> -. ( -. ph \/ -. ps ) )

  proof
    wph
    wps
    wa
    wph
    wn
    wps
    wn
    wo
    wn
    wph
    wps
    anor
    biimpi
end
