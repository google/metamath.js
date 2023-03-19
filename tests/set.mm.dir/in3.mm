include "wi.mm"
include "dfvd3i.mm"
include "dfvd2ir.mm"

theorem in3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume in3.1: |- (. ph ,. ps ,. ch ->. th ).


  assert |- (. ph ,. ps ->. ( ch -> th ) ).

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
    in3.1
    dfvd3i
    dfvd2ir
end
