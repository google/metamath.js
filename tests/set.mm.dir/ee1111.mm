include "wi.mm"
include "syl3c.mm"
include "mpd.mm"

theorem ee1111
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee1111.1: |- ( ph -> ps )
  assume ee1111.2: |- ( ph -> ch )
  assume ee1111.3: |- ( ph -> th )
  assume ee1111.4: |- ( ph -> ta )
  assume ee1111.5: |- ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) )


  assert |- ( ph -> et )

  proof
    wph
    wta
    wet
    ee1111.4
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    ee1111.1
    ee1111.2
    ee1111.3
    ee1111.5
    syl3c
    mpd
end
