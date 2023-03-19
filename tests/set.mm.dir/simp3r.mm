include "wa.mm"
include "simpr.mm"
include "3ad2ant3.mm"

theorem simp3r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> th )

  proof
    wch
    wth
    wa
    wph
    wth
    wps
    wch
    wth
    simpr
    3ad2ant3
end
