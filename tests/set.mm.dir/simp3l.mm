include "wa.mm"
include "simpl.mm"
include "3ad2ant3.mm"

theorem simp3l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> ch )

  proof
    wch
    wth
    wa
    wph
    wch
    wps
    wch
    wth
    simpl
    3ad2ant3
end
