include "wa.mm"
include "3expa.mm"
include "mpdan.mm"

theorem mpd3an3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpd3an3.2: |- ( ( ph /\ ps ) -> ch )
  assume mpd3an3.3: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ps ) -> th )

  proof
    wph
    wps
    wa
    wch
    wth
    mpd3an3.2
    wph
    wps
    wch
    wth
    mpd3an3.3
    3expa
    mpdan
end
