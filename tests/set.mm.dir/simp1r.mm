include "wa.mm"
include "simpr.mm"
include "3ad2ant1.mm"

theorem simp1r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ps )

  proof
    wph
    wps
    wa
    wch
    wps
    wth
    wph
    wps
    simpr
    3ad2ant1
end
