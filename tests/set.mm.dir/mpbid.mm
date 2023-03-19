include "biimpd.mm"
include "mpd.mm"

theorem mpbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
