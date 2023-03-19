include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "ex.mm"
include "mp3an1.mm"
include "imp.mm"

theorem mp3anl1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mp3anl1.1: |- ph
  assume mp3anl1.2: |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta )


  assert |- ( ( ( ps /\ ch ) /\ th ) -> ta )

  proof
    wps
    wch
    wa
    wth
    wta
    wph
    wps
    wch
    wth
    wta
    wi
    mp3anl1.1
    wph
    wps
    wch
    w3a
    wth
    wta
    mp3anl1.2
    ex
    mp3an1
    imp
end
