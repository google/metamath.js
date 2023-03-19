include "wi.mm"
include "wa.mm"
include "dfvd3i.mm"
include "exp4a.mm"
include "dfvd3ir.mm"

theorem in3an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume in3an.1: |- (. ph ,. ps ,. ( ch /\ th ) ->. ta ).


  assert |- (. ph ,. ps ,. ch ->. ( th -> ta ) ).

  proof
    wph
    wps
    wch
    wth
    wta
    wi
    wph
    wps
    wch
    wth
    wta
    wph
    wps
    wch
    wth
    wa
    wta
    in3an.1
    dfvd3i
    exp4a
    dfvd3ir
end
