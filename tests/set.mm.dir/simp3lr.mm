include "wa.mm"
include "simplr.mm"
include "3ad2ant3.mm"

theorem simp3lr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ps )

  proof
    wph
    wps
    wa
    wch
    wa
    wth
    wps
    wta
    wph
    wps
    wch
    simplr
    3ad2ant3
end
