include "wa.mm"
include "w3a.mm"
include "simp1l.mm"
include "3ad2ant3.mm"

theorem simp31l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph )

  proof
    wph
    wps
    wa
    wch
    wth
    w3a
    wta
    wph
    wet
    wph
    wps
    wch
    wth
    simp1l
    3ad2ant3
end
