include "wo.mm"
include "orc.mm"
include "syl.mm"

theorem orcd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume orcd.1: |- ( ph -> ps )


  assert |- ( ph -> ( ps \/ ch ) )

  proof
    wph
    wps
    wps
    wch
    wo
    orcd.1
    wps
    wch
    orc
    syl
end
