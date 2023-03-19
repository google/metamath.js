include "wi.mm"
include "imim1.mm"
include "imp.mm"

theorem pm3.33
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) /\ ( ps -> ch ) ) -> ( ph -> ch ) )

  proof
    wph
    wps
    wi
    wps
    wch
    wi
    wph
    wch
    wi
    wph
    wps
    wch
    imim1
    imp
end
