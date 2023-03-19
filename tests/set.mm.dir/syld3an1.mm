include "3com13.mm"
include "syld3an3.mm"

theorem syld3an1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syld3an1.1: |- ( ( ch /\ ps /\ th ) -> ph )
  assume syld3an1.2: |- ( ( ph /\ ps /\ th ) -> ta )


  assert |- ( ( ch /\ ps /\ th ) -> ta )

  proof
    wth
    wps
    wch
    wta
    wth
    wps
    wch
    wph
    wta
    wch
    wps
    wth
    wph
    syld3an1.1
    3com13
    wph
    wps
    wth
    wta
    syld3an1.2
    3com13
    syld3an3
    3com13
end
