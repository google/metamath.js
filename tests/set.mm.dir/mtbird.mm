include "biimpd.mm"
include "mtod.mm"

theorem mtbird
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mtbird.min: |- ( ph -> -. ch )
  assume mtbird.maj: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wch
    mtbird.min
    wph
    wps
    wch
    mtbird.maj
    biimpd
    mtod
end
