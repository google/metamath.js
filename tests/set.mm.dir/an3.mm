include "wa.mm"
include "an43.mm"
include "simplbi.mm"

theorem an3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ( ph /\ th ) )

  proof
    wph
    wps
    wa
    wch
    wth
    wa
    wa
    wph
    wth
    wa
    wps
    wch
    wa
    wph
    wps
    wch
    wth
    an43
    simplbi
end
