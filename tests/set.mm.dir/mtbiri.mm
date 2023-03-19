include "biimpd.mm"
include "mtoi.mm"

theorem mtbiri
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mtbiri.min: |- -. ch
  assume mtbiri.maj: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wch
    mtbiri.min
    wph
    wps
    wch
    mtbiri.maj
    biimpd
    mtoi
end
