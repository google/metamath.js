include "w3a.mm"
include "simp1.mm"
include "simp2.mm"
include "syl3anc.mm"

theorem syld3an3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syld3an3.1: |- ( ( ph /\ ps /\ ch ) -> th )
  assume syld3an3.2: |- ( ( ph /\ ps /\ th ) -> ta )


  assert |- ( ( ph /\ ps /\ ch ) -> ta )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wth
    wta
    wph
    wps
    wch
    simp1
    wph
    wps
    wch
    simp2
    syld3an3.1
    syld3an3.2
    syl3anc
end
