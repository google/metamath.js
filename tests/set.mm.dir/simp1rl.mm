include "wa.mm"
include "simprl.mm"
include "3ad2ant1.mm"

theorem simp1rl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ph )

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
    3ad2ant1
end
