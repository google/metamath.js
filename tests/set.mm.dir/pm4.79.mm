include "wi.mm"
include "wo.mm"
include "wa.mm"
include "id.mm"
include "jaoa.mm"
include "wn.mm"
include "simplim.mm"
include "pm3.3.mm"
include "syl5.mm"
include "orrd.mm"
include "impbii.mm"

theorem pm4.79
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ps -> ph ) \/ ( ch -> ph ) ) <-> ( ( ps /\ ch ) -> ph ) )

  proof
    wps
    wph
    wi
    #
    wch
    wph
    wi
    #
    wo
    wps
    wch
    wa
    wph
    wi
    #
    @0
    wps
    wph
    @1
    wch
    @0
    id
    @1
    id
    jaoa
    @2
    @0
    @1
    @0
    wn
    wps
    @2
    @1
    wps
    wph
    simplim
    wps
    wch
    wph
    pm3.3
    syl5
    orrd
    impbii
end
