include "wo.mm"
include "wa.mm"
include "andi.mm"
include "ancom.mm"
include "orbi12i.mm"
include "3bitr4i.mm"

theorem andir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph \/ ps ) /\ ch ) <-> ( ( ph /\ ch ) \/ ( ps /\ ch ) ) )

  proof
    wch
    wph
    wps
    wo
    #
    wa
    wch
    wph
    wa
    #
    wch
    wps
    wa
    #
    wo
    @0
    wch
    wa
    wph
    wch
    wa
    #
    wps
    wch
    wa
    #
    wo
    wch
    wph
    wps
    andi
    @0
    wch
    ancom
    @3
    @1
    @4
    @2
    wph
    wch
    ancom
    wps
    wch
    ancom
    orbi12i
    3bitr4i
end
