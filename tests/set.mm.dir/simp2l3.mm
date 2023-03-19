include "w3a.mm"
include "wa.mm"
include "simpl3.mm"
include "3ad2ant2.mm"

theorem simp2l3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ch )

  proof
    wph
    wps
    wch
    w3a
    wth
    wa
    wta
    wch
    wet
    wph
    wps
    wch
    wth
    simpl3
    3ad2ant2
end
