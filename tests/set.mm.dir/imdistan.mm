include "wi.mm"
include "wa.mm"
include "pm5.42.mm"
include "impexp.mm"
include "bitr4i.mm"

theorem imdistan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) <-> ( ( ph /\ ps ) -> ( ph /\ ch ) ) )

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
    #
    wi
    wi
    wph
    wps
    wa
    @0
    wi
    wph
    wps
    wch
    pm5.42
    wph
    wps
    @0
    impexp
    bitr4i
end
