include "wi.mm"
include "imdi.mm"
include "bicomi.mm"

theorem pm5.41
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) <-> ( ph -> ( ps -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    wph
    wps
    wi
    wph
    wch
    wi
    wi
    wph
    wps
    wch
    imdi
    bicomi
end
