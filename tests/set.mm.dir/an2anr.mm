include "wa.mm"
include "ancom.mm"
include "anbi12i.mm"

theorem an2anr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> ( ( ps /\ ph ) /\ ( th /\ ch ) ) )

  proof
    wph
    wps
    wa
    wps
    wph
    wa
    wch
    wth
    wa
    wth
    wch
    wa
    wph
    wps
    ancom
    wch
    wth
    ancom
    anbi12i
end
