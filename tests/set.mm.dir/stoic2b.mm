include "mpd3an3.mm"

theorem stoic2b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume stoic2b.1: |- ( ( ph /\ ps ) -> ch )
  assume stoic2b.2: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ps ) -> th )

  proof
    wph
    wps
    wch
    wth
    stoic2b.1
    stoic2b.2
    mpd3an3
end
