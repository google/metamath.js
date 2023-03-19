include "w3a.mm"
include "wa.mm"
include "an6.mm"
include "bicomi.mm"

theorem 3an6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) /\ ( ta /\ et ) ) <-> ( ( ph /\ ch /\ ta ) /\ ( ps /\ th /\ et ) ) )

  proof
    wph
    wch
    wta
    w3a
    wps
    wth
    wet
    w3a
    wa
    wph
    wps
    wa
    wch
    wth
    wa
    wta
    wet
    wa
    w3a
    wph
    wch
    wta
    wps
    wth
    wet
    an6
    bicomi
end
