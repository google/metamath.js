include "in1.mm"
include "a1d.mm"
include "a1dd.mm"
include "dfvd3ir.mm"

theorem vd13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume vd13.1: |- (. ph ->. ps ).


  assert |- (. ph ,. ch ,. th ->. ps ).

  proof
    wph
    wch
    wth
    wps
    wph
    wch
    wps
    wth
    wph
    wps
    wch
    wph
    wps
    vd13.1
    in1
    a1d
    a1dd
    dfvd3ir
end
