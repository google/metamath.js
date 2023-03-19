include "biimpi.mm"
include "syl3an3.mm"

theorem syl3an3b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl3an3b.1: |- ( ph <-> th )
  assume syl3an3b.2: |- ( ( ps /\ ch /\ th ) -> ta )


  assert |- ( ( ps /\ ch /\ ph ) -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    wph
    wth
    syl3an3b.1
    biimpi
    syl3an3b.2
    syl3an3
end
