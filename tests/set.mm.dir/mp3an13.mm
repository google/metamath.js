include "mp3an3.mm"
include "mpan.mm"

theorem mp3an13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mp3an13.1: |- ph
  assume mp3an13.2: |- ch
  assume mp3an13.3: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ps -> th )

  proof
    wph
    wps
    wth
    mp3an13.1
    wph
    wps
    wch
    wth
    mp3an13.2
    mp3an13.3
    mp3an3
    mpan
end
