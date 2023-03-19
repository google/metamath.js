include "wi.mm"
include "a1i.mm"
include "dfvd2ir.mm"

theorem vd02
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume vd02.1: |- ph


  assert |- (. ps ,. ch ->. ph ).

  proof
    wps
    wch
    wph
    wch
    wph
    wi
    wps
    wph
    wch
    vd02.1
    a1i
    a1i
    dfvd2ir
end
