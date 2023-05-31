include "com12.mm"
include "mpd.mm"

theorem mpcom
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume mpcom.1: |- ( ps -> ph )
  assume mpcom.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ps -> ch )

  proof
    wps
    wph
    wch
    mpcom.1
    wph
    wps
    wch
    mpcom.2
    com12
    mpd
end
