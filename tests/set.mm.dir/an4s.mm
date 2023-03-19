include "wa.mm"
include "an4.mm"
include "sylbi.mm"

theorem an4s
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume an4s.1: |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta )


  assert |- ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) -> ta )

  proof
    wph
    wch
    wa
    wps
    wth
    wa
    wa
    wph
    wps
    wa
    wch
    wth
    wa
    wa
    wta
    wph
    wch
    wps
    wth
    an4
    an4s.1
    sylbi
end
