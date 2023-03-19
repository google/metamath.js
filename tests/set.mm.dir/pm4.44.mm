include "wa.mm"
include "wo.mm"
include "orc.mm"
include "id.mm"
include "simpl.mm"
include "jaoi.mm"
include "impbii.mm"

theorem pm4.44
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph <-> ( ph \/ ( ph /\ ps ) ) )

  proof
    wph
    wph
    wph
    wps
    wa
    #
    wo
    wph
    @0
    orc
    wph
    wph
    @0
    wph
    id
    wph
    wps
    simpl
    jaoi
    impbii
end
