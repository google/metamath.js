include "biimpri.mm"
include "syl3an3.mm"

theorem syl3an3br
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl3an3br.1: |- ( th <-> ph )
  assume syl3an3br.2: |- ( ( ps /\ ch /\ th ) -> ta )


  assert |- ( ( ps /\ ch /\ ph ) -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    wth
    wph
    syl3an3br.1
    biimpri
    syl3an3br.2
    syl3an3
end
