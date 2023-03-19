include "biidd.mm"
include "3anbi12d.mm"

theorem 3anbi2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3anbi1d.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( th /\ ps /\ ta ) <-> ( th /\ ch /\ ta ) ) )

  proof
    wph
    wth
    wth
    wps
    wch
    wta
    wph
    wth
    biidd
    3anbi1d.1
    3anbi12d
end
