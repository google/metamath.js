include "w3a.mm"
include "3jca.mm"
include "mpd.mm"

theorem mp3and
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mp3and.1: |- ( ph -> ps )
  assume mp3and.2: |- ( ph -> ch )
  assume mp3and.3: |- ( ph -> th )
  assume mp3and.4: |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) )


  assert |- ( ph -> ta )

  proof
    wph
    wps
    wch
    wth
    w3a
    wta
    wph
    wps
    wch
    wth
    mp3and.1
    mp3and.2
    mp3and.3
    3jca
    mp3and.4
    mpd
end
