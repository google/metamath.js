include "biimprd.mm"
include "mtoi.mm"

theorem mtbii
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mtbii.min: |- -. ps
  assume mtbii.maj: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> -. ch )

  proof
    wph
    wch
    wps
    mtbii.min
    wph
    wps
    wch
    mtbii.maj
    biimprd
    mtoi
end
