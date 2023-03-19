include "wcad.mm"
include "wo.mm"
include "wa.mm"
include "cad1.mm"
include "cad0.mm"
include "casesifp.mm"

theorem cadifp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( cadd ( ph , ps , ch ) <-> if- ( ch , ( ph \/ ps ) , ( ph /\ ps ) ) )

  proof
    wch
    wph
    wps
    wch
    wcad
    wph
    wps
    wo
    wph
    wps
    wa
    wph
    wps
    wch
    cad1
    wph
    wps
    wch
    cad0
    casesifp
end
