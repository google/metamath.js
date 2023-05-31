include "wi.mm"
include "a2d.mm"
include "mpd.mm"

theorem mpdd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume mpdd.1: |- ( ph -> ( ps -> ch ) )
  assume mpdd.2: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wth
    wi
    mpdd.1
    wph
    wps
    wch
    wth
    mpdd.2
    a2d
    mpd
end
