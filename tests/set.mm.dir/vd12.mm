include "in1.mm"
include "a1d.mm"
include "dfvd2ir.mm"

theorem vd12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume vd12.1: |- (. ph ->. ps ).


  assert |- (. ph ,. ch ->. ps ).

  proof
    wph
    wch
    wps
    wph
    wps
    wch
    wph
    wps
    vd12.1
    in1
    a1d
    dfvd2ir
end
