include "wa.mm"
include "simpr.mm"
include "imim1i.mm"

theorem pm3.42
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ps -> ch ) -> ( ( ph /\ ps ) -> ch ) )

  proof
    wph
    wps
    wa
    wps
    wch
    wph
    wps
    simpr
    imim1i
end
