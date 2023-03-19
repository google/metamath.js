include "mpi.mm"
include "syl6.mm"

theorem syl6mpi
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume syl6mpi.1: |- ( ph -> ( ps -> ch ) )
  assume syl6mpi.2: |- th
  assume syl6mpi.3: |- ( ch -> ( th -> ta ) )


  assert |- ( ph -> ( ps -> ta ) )

  proof
    wph
    wps
    wch
    wta
    syl6mpi.1
    wch
    wth
    wta
    syl6mpi.2
    syl6mpi.3
    mpi
    syl6
end
