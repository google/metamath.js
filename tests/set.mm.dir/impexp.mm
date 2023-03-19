include "wa.mm"
include "wi.mm"
include "pm3.3.mm"
include "pm3.31.mm"
include "impbii.mm"

theorem impexp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) )

  proof
    wph
    wps
    wa
    wch
    wi
    wph
    wps
    wch
    wi
    wi
    wph
    wps
    wch
    pm3.3
    wph
    wps
    wch
    pm3.31
    impbii
end
