include "wo.mm"
include "orc.mm"
include "syl.mm"

theorem orcd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
