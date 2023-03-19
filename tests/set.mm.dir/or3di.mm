include "w3a.mm"
include "wo.mm"
include "wa.mm"
include "df-3an.mm"
include "orbi2i.mm"
include "ordi.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "bitr4i.mm"

theorem or3di
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta


  assert |- ( ( ph \/ ( ps /\ ch /\ ta ) ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) /\ ( ph \/ ta ) ) )

  proof
    wph
    wps
    wch
    wta
    w3a
    #
    wo
    #
    wph
    wps
    wo
    #
    wph
    wch
    wo
    #
    wa
    #
    wph
    wta
    wo
    #
    wa
    #
    @2
    @3
    @5
    w3a
    @1
    wph
    wps
    wch
    wa
    #
    wta
    wa
    #
    wo
    wph
    @7
    wo
    #
    @5
    wa
    @6
    @0
    @8
    wph
    wps
    wch
    wta
    df-3an
    orbi2i
    wph
    @7
    wta
    ordi
    @9
    @4
    @5
    wph
    wps
    wch
    ordi
    anbi1i
    3bitri
    @2
    @3
    @5
    df-3an
    bitr4i
end
