include "wi.mm"
include "dfvd2ani.mm"
include "ex.mm"
include "dfvd1ir.mm"

theorem int2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume int2.1: |- (. (. ph ,. ps ). ->. ch ).


  assert |- (. ph ->. ( ps -> ch ) ).

  proof
    wph
    wps
    wch
    wi
    wph
    wps
    wch
    wph
    wps
    wch
    int2.1
    dfvd2ani
    ex
    dfvd1ir
end
