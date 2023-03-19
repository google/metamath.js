include "biidd.mm"
include "3anbi123d.mm"

theorem 3anbi13d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume 3anbi12d.1: |- ( ph -> ( ps <-> ch ) )
  assume 3anbi12d.2: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ( ps /\ et /\ th ) <-> ( ch /\ et /\ ta ) ) )

  proof
    wph
    wps
    wch
    wet
    wet
    wth
    wta
    3anbi12d.1
    wph
    wet
    biidd
    3anbi12d.2
    3anbi123d
end
