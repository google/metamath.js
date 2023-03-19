include "wi.mm"
include "wa.mm"
include "pm5.42.mm"
include "biimpi.mm"

theorem anc2l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ph /\ ch ) ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    wph
    wps
    wph
    wch
    wa
    wi
    wi
    wph
    wps
    wch
    pm5.42
    biimpi
end
