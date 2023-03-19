include "wa.mm"
include "w3a.mm"
include "ancoms.mm"
include "mp3anl3.mm"

theorem mp3anr3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mp3anr3.1: |- th
  assume mp3anr3.2: |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta )


  assert |- ( ( ph /\ ( ps /\ ch ) ) -> ta )

  proof
    wps
    wch
    wa
    wph
    wta
    wps
    wch
    wth
    wph
    wta
    mp3anr3.1
    wph
    wps
    wch
    wth
    w3a
    wta
    mp3anr3.2
    ancoms
    mp3anl3
    ancoms
end
