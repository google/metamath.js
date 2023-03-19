include "a1i.mm"
include "mpbid.mm"

theorem mpbii
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mpbii.min: |- ps
  assume mpbii.maj: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    wps
    wph
    mpbii.min
    a1i
    mpbii.maj
    mpbid
end
