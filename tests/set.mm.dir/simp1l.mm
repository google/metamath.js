include "wa.mm"
include "simpl.mm"
include "3ad2ant1.mm"

theorem simp1l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ph )

  proof
    wph
    wps
    wa
    wch
    wph
    wth
    wph
    wps
    simpl
    3ad2ant1
end
