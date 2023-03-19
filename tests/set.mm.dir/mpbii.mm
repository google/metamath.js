include "a1i.mm"
include "mpbid.mm"

theorem mpbii
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
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
