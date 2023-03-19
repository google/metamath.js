include "biimpri.mm"
include "syl3an2.mm"

theorem syl3an2br
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl3an2br.1: |- ( ch <-> ph )
  assume syl3an2br.2: |- ( ( ps /\ ch /\ th ) -> ta )


  assert |- ( ( ps /\ ph /\ th ) -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    wch
    wph
    syl3an2br.1
    biimpri
    syl3an2br.2
    syl3an2
end
