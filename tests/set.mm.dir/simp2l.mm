include "wa.mm"
include "simpl.mm"
include "3ad2ant2.mm"

theorem simp2l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ps )

  proof
    wps
    wch
    wa
    wph
    wps
    wth
    wps
    wch
    simpl
    3ad2ant2
end
