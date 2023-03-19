include "id.mm"
include "syl3anc.mm"

theorem mpd3an23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpd3an23.1: |- ( ph -> ps )
  assume mpd3an23.2: |- ( ph -> ch )
  assume mpd3an23.3: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wph
    wps
    wch
    wth
    wph
    id
    mpd3an23.1
    mpd3an23.2
    mpd3an23.3
    syl3anc
end
