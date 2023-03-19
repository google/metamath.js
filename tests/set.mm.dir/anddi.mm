include "wo.mm"
include "wa.mm"
include "andir.mm"
include "andi.mm"
include "orbi12i.mm"
include "bitri.mm"

theorem anddi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph \/ ps ) /\ ( ch \/ th ) ) <-> ( ( ( ph /\ ch ) \/ ( ph /\ th ) ) \/ ( ( ps /\ ch ) \/ ( ps /\ th ) ) ) )

  proof
    wph
    wps
    wo
    wch
    wth
    wo
    #
    wa
    wph
    @0
    wa
    #
    wps
    @0
    wa
    #
    wo
    wph
    wch
    wa
    wph
    wth
    wa
    wo
    #
    wps
    wch
    wa
    wps
    wth
    wa
    wo
    #
    wo
    wph
    wps
    @0
    andir
    @1
    @3
    @2
    @4
    wph
    wch
    wth
    andi
    wps
    wch
    wth
    andi
    orbi12i
    bitri
end
