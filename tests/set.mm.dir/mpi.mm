include "a1i.mm"
include "mpd.mm"

theorem mpi
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume mpi.1: |- ps
  assume mpi.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    wps
    wph
    mpi.1
    a1i
    mpi.2
    mpd
end
