include "3com23.mm"
include "syld3an3.mm"

theorem syld3an2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syld3an2.1: |- ( ( ph /\ ch /\ th ) -> ps )
  assume syld3an2.2: |- ( ( ph /\ ps /\ th ) -> ta )


  assert |- ( ( ph /\ ch /\ th ) -> ta )

  proof
    wph
    wth
    wch
    wta
    wph
    wth
    wch
    wps
    wta
    wph
    wch
    wth
    wps
    syld3an2.1
    3com23
    wph
    wps
    wth
    wta
    syld3an2.2
    3com23
    syld3an3
    3com23
end
