include "mp3an1.mm"
include "mp2an.mm"

theorem mp3an
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume mp3an.1: |- ph
  assume mp3an.2: |- ps
  assume mp3an.3: |- ch
  assume mp3an.4: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- th

  proof
    wps
    wch
    wth
    mp3an.2
    mp3an.3
    wph
    wps
    wch
    wth
    mp3an.1
    mp3an.4
    mp3an1
    mp2an
end
