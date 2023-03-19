include "wa.mm"
include "w3a.mm"
include "ancoms.mm"
include "mp3anl1.mm"

theorem mp3anr1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mp3anr1.1: |- ps
  assume mp3anr1.2: |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta )


  assert |- ( ( ph /\ ( ch /\ th ) ) -> ta )

  proof
    wch
    wth
    wa
    wph
    wta
    wps
    wch
    wth
    wph
    wta
    mp3anr1.1
    wph
    wps
    wch
    wth
    w3a
    wta
    mp3anr1.2
    ancoms
    mp3anl1
    ancoms
end
