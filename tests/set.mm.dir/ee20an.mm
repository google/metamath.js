include "ex.mm"
include "syl6mpi.mm"

theorem ee20an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ee20an.1: |- ( ph -> ( ps -> ch ) )
  assume ee20an.2: |- th
  assume ee20an.3: |- ( ( ch /\ th ) -> ta )


  assert |- ( ph -> ( ps -> ta ) )

  proof
    wph
    wps
    wch
    wth
    wta
    ee20an.1
    ee20an.2
    wch
    wth
    wta
    ee20an.3
    ex
    syl6mpi
end
