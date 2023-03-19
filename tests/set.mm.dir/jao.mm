include "wi.mm"
include "wo.mm"
include "pm3.44.mm"
include "ex.mm"

theorem jao
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ch -> ps ) -> ( ( ph \/ ch ) -> ps ) ) )

  proof
    wph
    wps
    wi
    wch
    wps
    wi
    wph
    wch
    wo
    wps
    wi
    wps
    wph
    wch
    pm3.44
    ex
end
