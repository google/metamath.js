include "in1.mm"
include "syl.mm"
include "dfvd1ir.mm"

theorem e1a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume e1a.1: |- (. ph ->. ps ).
  assume e1a.2: |- ( ps -> ch )


  assert |- (. ph ->. ch ).

  proof
    wph
    wch
    wph
    wps
    wch
    wph
    wps
    e1a.1
    in1
    e1a.2
    syl
    dfvd1ir
end
