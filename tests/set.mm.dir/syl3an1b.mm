include "biimpi.mm"
include "syl3an1.mm"

theorem syl3an1b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl3an1b.1: |- ( ph <-> ps )
  assume syl3an1b.2: |- ( ( ps /\ ch /\ th ) -> ta )


  assert |- ( ( ph /\ ch /\ th ) -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    wph
    wps
    syl3an1b.1
    biimpi
    syl3an1b.2
    syl3an1
end
