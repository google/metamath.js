include "wi.mm"
include "imim2.mm"
include "imp.mm"

theorem pm3.34
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ps -> ch ) /\ ( ph -> ps ) ) -> ( ph -> ch ) )

  proof
    wps
    wch
    wi
    wph
    wps
    wi
    wph
    wch
    wi
    wps
    wch
    wph
    imim2
    imp
end
