include "wa.mm"
include "simpll.mm"
include "3ad2ant3.mm"

theorem simp3ll
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ph )

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
    3ad2ant3
end
