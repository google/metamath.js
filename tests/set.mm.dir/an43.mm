include "wa.mm"
include "an42.mm"
include "bicomi.mm"

theorem an43
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> ( ( ph /\ th ) /\ ( ps /\ ch ) ) )

  proof
    wph
    wth
    wa
    wps
    wch
    wa
    wa
    wph
    wps
    wa
    wch
    wth
    wa
    wa
    wph
    wth
    wps
    wch
    an42
    bicomi
end
