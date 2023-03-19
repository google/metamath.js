include "wo.mm"
include "wa.mm"
include "w3o.mm"
include "andi.mm"
include "orbi1i.mm"
include "bitri.mm"
include "df-3or.mm"
include "anbi2i.mm"
include "3bitr4i.mm"

theorem andi3or
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ( ps \/ ch \/ th ) ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) \/ ( ph /\ th ) ) )

  proof
    wph
    wps
    wch
    wo
    #
    wth
    wo
    #
    wa
    #
    wph
    wps
    wa
    #
    wph
    wch
    wa
    #
    wo
    #
    wph
    wth
    wa
    #
    wo
    #
    wph
    wps
    wch
    wth
    w3o
    #
    wa
    @3
    @4
    @6
    w3o
    @2
    wph
    @0
    wa
    #
    @6
    wo
    @7
    wph
    @0
    wth
    andi
    @9
    @5
    @6
    wph
    wps
    wch
    andi
    orbi1i
    bitri
    @8
    @1
    wph
    wps
    wch
    wth
    df-3or
    anbi2i
    @3
    @4
    @6
    df-3or
    3bitr4i
end
