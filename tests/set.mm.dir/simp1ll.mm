include "wa.mm"
include "simpll.mm"
include "3ad2ant1.mm"

theorem simp1ll
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ph )

  proof
    wph
    wps
    wa
    wch
    wa
    wth
    wph
    wta
    wph
    wps
    wch
    simpll
    3ad2ant1
end
