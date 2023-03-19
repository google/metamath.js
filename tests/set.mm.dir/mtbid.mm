include "biimprd.mm"
include "mtod.mm"

theorem mtbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mtbid.min: |- ( ph -> -. ps )
  assume mtbid.maj: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> -. ch )

  proof
    wph
    wch
    wps
    mtbid.min
    wph
    wps
    wch
    mtbid.maj
    biimprd
    mtod
end
