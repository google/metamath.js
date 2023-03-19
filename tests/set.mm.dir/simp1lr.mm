include "wa.mm"
include "simplr.mm"
include "3ad2ant1.mm"

theorem simp1lr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ps )

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
    3ad2ant1
end
