include "biidd.mm"
include "3anbi123d.mm"

theorem 3anbi12d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume 3anbi12d.1: |- ( ph -> ( ps <-> ch ) )
  assume 3anbi12d.2: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ et ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wet
    3anbi12d.1
    3anbi12d.2
    wph
    wet
    biidd
    3anbi123d
end
