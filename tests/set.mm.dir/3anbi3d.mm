include "biidd.mm"
include "3anbi13d.mm"

theorem 3anbi3d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3anbi1d.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( th /\ ta /\ ps ) <-> ( th /\ ta /\ ch ) ) )

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
    3anbi13d
end
