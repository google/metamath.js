include "wi.mm"
include "dfvd3ani.mm"
include "3expia.mm"
include "dfvd2anir.mm"

theorem int3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume int3.1: |- (. (. ph ,. ps ,. ch ). ->. th ).


  assert |- (. (. ph ,. ps ). ->. ( ch -> th ) ).

  proof
    wph
    wps
    wch
    wth
    wi
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    int3.1
    dfvd3ani
    3expia
    dfvd2anir
end
