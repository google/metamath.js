include "wa.mm"
include "mp3an3an.mm"
include "anabss5.mm"

theorem mp3an2ani
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume mp3an2ani.1: |- ph
  assume mp3an2ani.2: |- ( ps -> ch )
  assume mp3an2ani.3: |- ( ( ps /\ th ) -> ta )
  assume mp3an2ani.4: |- ( ( ph /\ ch /\ ta ) -> et )


  assert |- ( ( ps /\ th ) -> et )

  proof
    wps
    wth
    wet
    wph
    wps
    wch
    wps
    wth
    wa
    wta
    wet
    mp3an2ani.1
    mp3an2ani.2
    mp3an2ani.3
    mp3an2ani.4
    mp3an3an
    anabss5
end
