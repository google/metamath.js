include "wvhc3.mm"
include "wvd1.mm"
include "w3a.mm"
include "wi.mm"
include "dfvd3an.mm"
include "mpbi.mm"

theorem dfvd3ani
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume dfvd3ani.1: |- (. (. ph ,. ps ,. ch ). ->. th ).


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wvhc3
    wth
    wvd1
    wph
    wps
    wch
    w3a
    wth
    wi
    dfvd3ani.1
    wph
    wps
    wch
    wth
    dfvd3an
    mpbi
end
