include "biimpd.mm"
include "mpd.mm"

theorem mpbid
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume mpbid.min: |- ( ph -> ps )
  assume mpbid.maj: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    mpbid.min
    wph
    wps
    wch
    mpbid.maj
    biimpd
    mpd
end
