include "wcad.mm"
include "wo.mm"
include "wa.mm"
include "w3a.mm"
include "w3o.mm"
include "df-3or.mm"
include "cador.mm"
include "andi.mm"
include "orbi1i.mm"
include "3bitr4i.mm"
include "ordir.mm"
include "ordi.mm"
include "orcom.mm"
include "wi.mm"
include "wb.mm"
include "animorl.mm"
include "pm4.72.mm"
include "mpbi.mm"
include "bitr4i.mm"
include "anbi12i.mm"
include "3bitri.mm"
include "df-3an.mm"

theorem cadan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( cadd ( ph , ps , ch ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) /\ ( ps \/ ch ) ) )

  proof
    wph
    wps
    wch
    wcad
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
    wps
    wch
    wo
    #
    wa
    #
    @1
    @2
    @4
    w3a
    @0
    wph
    @4
    wa
    #
    wps
    wch
    wa
    #
    wo
    #
    wph
    @7
    wo
    #
    @4
    @7
    wo
    #
    wa
    @5
    wph
    wps
    wa
    #
    wph
    wch
    wa
    #
    @7
    w3o
    @11
    @12
    wo
    #
    @7
    wo
    @0
    @8
    @11
    @12
    @7
    df-3or
    wph
    wps
    wch
    cador
    @6
    @13
    @7
    wph
    wps
    wch
    andi
    orbi1i
    3bitr4i
    wph
    @4
    @7
    ordir
    @9
    @3
    @10
    @4
    wph
    wps
    wch
    ordi
    @10
    @7
    @4
    wo
    #
    @4
    @4
    @7
    orcom
    @7
    @4
    wi
    @4
    @14
    wb
    wps
    wch
    wch
    animorl
    @7
    @4
    pm4.72
    mpbi
    bitr4i
    anbi12i
    3bitri
    @1
    @2
    @4
    df-3an
    bitr4i
end
