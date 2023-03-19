include "dfvd2i.mm"
include "a1dd.mm"
include "dfvd3ir.mm"

theorem vd23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume vd23.1: |- (. ph ,. ps ->. ch ).


  assert |- (. ph ,. ps ,. th ->. ch ).

  proof
    wph
    wps
    wth
    wch
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    vd23.1
    dfvd2i
    a1dd
    dfvd3ir
end
