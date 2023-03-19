include "biidd.mm"
include "3anbi12d.mm"

theorem 3anbi1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3anbi1d.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( ps /\ th /\ ta ) <-> ( ch /\ th /\ ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wth
    wta
    3anbi1d.1
    wph
    wth
    biidd
    3anbi12d
end
