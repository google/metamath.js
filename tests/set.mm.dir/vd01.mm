include "a1i.mm"
include "dfvd1ir.mm"

theorem vd01
  let wph: wff ph
  let wps: wff ps
  assume vd01.1: |- ph


  assert |- (. ps ->. ph ).

  proof
    wps
    wph
    wph
    wps
    vd01.1
    a1i
    dfvd1ir
end
