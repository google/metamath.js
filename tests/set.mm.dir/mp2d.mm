include "mpid.mm"
include "mpd.mm"

theorem mp2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mp2d.1: |- ( ph -> ps )
  assume mp2d.2: |- ( ph -> ch )
  assume mp2d.3: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wth
    mp2d.1
    wph
    wps
    wch
    wth
    mp2d.2
    mp2d.3
    mpid
    mpd
end
