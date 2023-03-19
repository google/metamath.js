include "wa.mm"
include "an4.mm"
include "sylbi.mm"

theorem an4s
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
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
