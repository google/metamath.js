include "biimpri.mm"
include "syl3an1.mm"

theorem syl3an1br
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl3an1br.1: |- ( ps <-> ph )
  assume syl3an1br.2: |- ( ( ps /\ ch /\ th ) -> ta )


  assert |- ( ( ph /\ ch /\ th ) -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    wps
    wph
    syl3an1br.1
    biimpri
    syl3an1br.2
    syl3an1
end
