include "w3a.mm"
include "wa.mm"
include "simpl1.mm"
include "3ad2ant3.mm"

theorem simp3l1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph )

  proof
    wph
    wps
    wch
    w3a
    wth
    wa
    wta
    wph
    wet
    wph
    wps
    wch
    wth
    simpl1
    3ad2ant3
end
