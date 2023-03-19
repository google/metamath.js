include "wi.mm"
include "exp41.mm"
include "syl3c.mm"
include "mpd.mm"

theorem eel1111
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume eel1111.1: |- ( ph -> ps )
  assume eel1111.2: |- ( ph -> ch )
  assume eel1111.3: |- ( ph -> th )
  assume eel1111.4: |- ( ph -> ta )
  assume eel1111.5: |- ( ( ( ( ps /\ ch ) /\ th ) /\ ta ) -> et )


  assert |- ( ph -> et )

  proof
    wph
    wta
    wet
    eel1111.4
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    eel1111.1
    eel1111.2
    eel1111.3
    wps
    wch
    wth
    wta
    wet
    eel1111.5
    exp41
    syl3c
    mpd
end
