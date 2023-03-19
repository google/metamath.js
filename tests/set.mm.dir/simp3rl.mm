include "wa.mm"
include "simprl.mm"
include "3ad2ant3.mm"

theorem simp3rl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ph )

  proof
    wch
    wph
    wps
    wa
    wa
    wth
    wph
    wta
    wch
    wph
    wps
    simprl
    3ad2ant3
end
