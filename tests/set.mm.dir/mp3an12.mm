include "mp3an1.mm"
include "mpan.mm"

theorem mp3an12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mp3an12.1: |- ph
  assume mp3an12.2: |- ps
  assume mp3an12.3: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ch -> th )

  proof
    wps
    wch
    wth
    mp3an12.2
    wph
    wps
    wch
    wth
    mp3an12.1
    mp3an12.3
    mp3an1
    mpan
end
