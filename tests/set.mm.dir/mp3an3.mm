include "wa.mm"
include "3expia.mm"
include "mpi.mm"

theorem mp3an3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mp3an3.1: |- ch
  assume mp3an3.2: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ps ) -> th )

  proof
    wph
    wps
    wa
    wch
    wth
    mp3an3.1
    wph
    wps
    wch
    wth
    mp3an3.2
    3expia
    mpi
end
