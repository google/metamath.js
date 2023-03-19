include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "ex.mm"
include "mp3an3.mm"
include "imp.mm"

theorem mp3anl3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mp3anl3.1: |- ch
  assume mp3anl3.2: |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta )


  assert |- ( ( ( ph /\ ps ) /\ th ) -> ta )

  proof
    wph
    wps
    wa
    wth
    wta
    wph
    wps
    wch
    wth
    wta
    wi
    mp3anl3.1
    wph
    wps
    wch
    w3a
    wth
    wta
    mp3anl3.2
    ex
    mp3an3
    imp
end
