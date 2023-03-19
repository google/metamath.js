include "wa.mm"
include "3expb.mm"
include "mpan.mm"

theorem mp3an1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mp3an1.1: |- ph
  assume mp3an1.2: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wa
    wth
    mp3an1.1
    wph
    wps
    wch
    wth
    mp3an1.2
    3expb
    mpan
end
