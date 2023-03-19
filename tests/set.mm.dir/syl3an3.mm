include "3exp.mm"
include "syl7.mm"
include "3imp.mm"

theorem syl3an3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl3an3.1: |- ( ph -> th )
  assume syl3an3.2: |- ( ( ps /\ ch /\ th ) -> ta )


  assert |- ( ( ps /\ ch /\ ph ) -> ta )

  proof
    wps
    wch
    wph
    wta
    wph
    wth
    wps
    wch
    wta
    syl3an3.1
    wps
    wch
    wth
    wta
    syl3an3.2
    3exp
    syl7
    3imp
end
