include "biidd.mm"
include "3anbi123d.mm"

theorem 3anbi23d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume 3anbi12d.1: |- ( ph -> ( ps <-> ch ) )
  assume 3anbi12d.2: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ( et /\ ps /\ th ) <-> ( et /\ ch /\ ta ) ) )

  proof
    wph
    wet
    wet
    wps
    wch
    wth
    wta
    wph
    wet
    biidd
    3anbi12d.1
    3anbi12d.2
    3anbi123d
end
