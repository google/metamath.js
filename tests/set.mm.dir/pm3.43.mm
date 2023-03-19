include "wi.mm"
include "wa.mm"
include "pm3.43i.mm"
include "imp.mm"

theorem pm3.43
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) -> ( ph -> ( ps /\ ch ) ) )

  proof
    wph
    wps
    wi
    wph
    wch
    wi
    wph
    wps
    wch
    wa
    wi
    wph
    wps
    wch
    pm3.43i
    imp
end
