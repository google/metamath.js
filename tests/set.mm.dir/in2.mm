include "wi.mm"
include "dfvd2i.mm"
include "dfvd1ir.mm"

theorem in2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume in2.1: |- (. ph ,. ps ->. ch ).


  assert |- (. ph ->. ( ps -> ch ) ).

  proof
    wph
    wps
    wch
    wi
    wph
    wps
    wch
    in2.1
    dfvd2i
    dfvd1ir
end
