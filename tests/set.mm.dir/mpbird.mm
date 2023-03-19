include "biimprd.mm"
include "mpd.mm"

theorem mpbird
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mpbird.min: |- ( ph -> ch )
  assume mpbird.maj: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ps )

  proof
    wph
    wch
    wps
    mpbird.min
    wph
    wps
    wch
    mpbird.maj
    biimprd
    mpd
end
