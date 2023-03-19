include "mp3an3.mm"
include "mpan2.mm"

theorem mp3an23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mp3an23.1: |- ps
  assume mp3an23.2: |- ch
  assume mp3an23.3: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wth
    mp3an23.1
    wph
    wps
    wch
    wth
    mp3an23.2
    mp3an23.3
    mp3an3
    mpan2
end
