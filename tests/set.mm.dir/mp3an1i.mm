include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "com12.mm"
include "mp3an1.mm"

theorem mp3an1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mp3an1i.1: |- ps
  assume mp3an1i.2: |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) )


  assert |- ( ph -> ( ( ch /\ th ) -> ta ) )

  proof
    wch
    wth
    wa
    wph
    wta
    wps
    wch
    wth
    wph
    wta
    wi
    mp3an1i.1
    wph
    wps
    wch
    wth
    w3a
    wta
    mp3an1i.2
    com12
    mp3an1
    com12
end
