include "wa.mm"
include "w3a.mm"
include "ancoms.mm"
include "mp3anl2.mm"

theorem mp3anr2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mp3anr2.1: |- ch
  assume mp3anr2.2: |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta )


  assert |- ( ( ph /\ ( ps /\ th ) ) -> ta )

  proof
    wps
    wth
    wa
    wph
    wta
    wps
    wch
    wth
    wph
    wta
    mp3anr2.1
    wph
    wps
    wch
    wth
    w3a
    wta
    mp3anr2.2
    ancoms
    mp3anl2
    ancoms
end
