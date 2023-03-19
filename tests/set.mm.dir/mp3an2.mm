include "3expa.mm"
include "mpanl2.mm"

theorem mp3an2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mp3an2.1: |- ps
  assume mp3an2.2: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    mp3an2.1
    wph
    wps
    wch
    wth
    mp3an2.2
    3expa
    mpanl2
end
