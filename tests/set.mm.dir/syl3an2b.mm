include "biimpi.mm"
include "syl3an2.mm"

theorem syl3an2b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl3an2b.1: |- ( ph <-> ch )
  assume syl3an2b.2: |- ( ( ps /\ ch /\ th ) -> ta )


  assert |- ( ( ps /\ ph /\ th ) -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    wph
    wch
    syl3an2b.1
    biimpi
    syl3an2b.2
    syl3an2
end
