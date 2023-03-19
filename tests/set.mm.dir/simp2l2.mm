include "w3a.mm"
include "wa.mm"
include "simpl2.mm"
include "3ad2ant2.mm"

theorem simp2l2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ps )

  proof
    wph
    wps
    wch
    w3a
    wth
    wa
    wta
    wps
    wet
    wph
    wps
    wch
    wth
    simpl2
    3ad2ant2
end
