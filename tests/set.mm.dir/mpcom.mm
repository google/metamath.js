include "com12.mm"
include "mpd.mm"

theorem mpcom
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
