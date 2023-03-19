include "wa.mm"
include "simprr.mm"
include "3ad2ant1.mm"

theorem simp1rr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ps )

  proof
    wch
    wph
    wps
    wa
    wa
    wth
    wps
    wta
    wch
    wph
    wps
    simprr
    3ad2ant1
end
