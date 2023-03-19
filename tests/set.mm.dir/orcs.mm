include "wo.mm"
include "orc.mm"
include "syl.mm"

theorem orcs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume orcs.1: |- ( ( ph \/ ps ) -> ch )


  assert |- ( ph -> ch )

  proof
    wph
    wph
    wps
    wo
    wch
    wph
    wps
    orc
    orcs.1
    syl
end
