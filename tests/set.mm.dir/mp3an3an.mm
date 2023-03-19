include "mp3an1.mm"
include "syl2an.mm"

theorem mp3an3an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume mp3an3an.1: |- ph
  assume mp3an3an.2: |- ( ps -> ch )
  assume mp3an3an.3: |- ( th -> ta )
  assume mp3an3an.4: |- ( ( ph /\ ch /\ ta ) -> et )


  assert |- ( ( ps /\ th ) -> et )

  proof
    wps
    wch
    wta
    wet
    wth
    mp3an3an.2
    mp3an3an.3
    wph
    wch
    wta
    wet
    mp3an3an.1
    mp3an3an.4
    mp3an1
    syl2an
end
