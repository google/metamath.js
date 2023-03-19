include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "ex.mm"
include "mp3an2.mm"
include "imp.mm"

theorem mp3anl2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mp3anl2.1: |- ps
  assume mp3anl2.2: |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta )


  assert |- ( ( ( ph /\ ch ) /\ th ) -> ta )

  proof
    wph
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
    mp3anl2.1
    wph
    wps
    wch
    w3a
    wth
    wta
    mp3anl2.2
    ex
    mp3an2
    imp
end
