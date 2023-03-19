include "in1.mm"
include "syl.mm"
include "dfvd1ir.mm"

theorem el1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume el1.1: |- (. ph ->. ps ).
  assume el1.2: |- ( ps -> ch )


  assert |- (. ph ->. ch ).

  proof
    wph
    wch
    wph
    wps
    wch
    wph
    wps
    el1.1
    in1
    el1.2
    syl
    dfvd1ir
end
