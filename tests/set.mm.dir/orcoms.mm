include "wo.mm"
include "pm1.4.mm"
include "syl.mm"

theorem orcoms
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume orcoms.1: |- ( ( ph \/ ps ) -> ch )


  assert |- ( ( ps \/ ph ) -> ch )

  proof
    wps
    wph
    wo
    wph
    wps
    wo
    wch
    wps
    wph
    pm1.4
    orcoms.1
    syl
end
