include "wi.mm"
include "wa.mm"
include "ax-1.mm"
include "ancli.mm"
include "simpl.mm"
include "impbii.mm"

theorem pm4.45im
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph <-> ( ph /\ ( ps -> ph ) ) )

  proof
    wph
    wph
    wps
    wph
    wi
    #
    wa
    wph
    @0
    wph
    wps
    ax-1
    ancli
    wph
    @0
    simpl
    impbii
end
