include "wa.mm"
include "wn.mm"
include "wo.mm"
include "anor.mm"
include "biimpri.mm"

theorem pm3.11
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( -. ph \/ -. ps ) -> ( ph /\ ps ) )

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
    biimpri
end
