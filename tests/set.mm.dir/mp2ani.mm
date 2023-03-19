include "mpani.mm"
include "mpi.mm"

theorem mp2ani
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mp2ani.1: |- ps
  assume mp2ani.2: |- ch
  assume mp2ani.3: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ph -> th )

  proof
    wph
    wch
    wth
    mp2ani.2
    wph
    wps
    wch
    wth
    mp2ani.1
    mp2ani.3
    mpani
    mpi
end
