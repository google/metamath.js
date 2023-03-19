include "wa.mm"
include "wi.mm"
include "impexp.mm"
include "imdistan.mm"
include "bitri.mm"

theorem pm5.3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ ps ) -> ( ph /\ ch ) ) )

  proof
    wph
    wps
    wa
    #
    wch
    wi
    wph
    wps
    wch
    wi
    wi
    @0
    wph
    wch
    wa
    wi
    wph
    wps
    wch
    impexp
    wph
    wps
    wch
    imdistan
    bitri
end
