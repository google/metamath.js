include "wa.mm"
include "an4s.mm"
include "ancom2s.mm"

theorem an42s
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume an41r3s.1: |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta )


  assert |- ( ( ( ph /\ ch ) /\ ( th /\ ps ) ) -> ta )

  proof
    wph
    wch
    wa
    wps
    wth
    wta
    wph
    wps
    wch
    wth
    wta
    an41r3s.1
    an4s
    ancom2s
end
