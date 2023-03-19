include "wi.mm"
include "sylc.mm"
include "mpd.mm"

theorem syl3c
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl3c.1: |- ( ph -> ps )
  assume syl3c.2: |- ( ph -> ch )
  assume syl3c.3: |- ( ph -> th )
  assume syl3c.4: |- ( ps -> ( ch -> ( th -> ta ) ) )


  assert |- ( ph -> ta )

  proof
    wph
    wth
    wta
    syl3c.3
    wph
    wps
    wch
    wth
    wta
    wi
    syl3c.1
    syl3c.2
    syl3c.4
    sylc
    mpd
end
