include "wa.mm"
include "simpll.mm"
include "3ad2ant2.mm"

theorem simp2ll
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ph )

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
    3ad2ant2
end
