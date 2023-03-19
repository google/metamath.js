include "wnan.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wxo.mm"
include "wb.mm"
include "df-nan.mm"
include "xor2.mm"
include "rbaibr.mm"
include "bibi2i.mm"
include "wi.mm"
include "pm4.71.mm"
include "simpl.mm"
include "orcd.mm"
include "con3i.mm"
include "id.mm"
include "ja.mm"
include "sylbir.mm"
include "sylbi.mm"
include "impbii.mm"
include "bitri.mm"

theorem nanorxor
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -/\ ps ) <-> ( ( ph \/ ps ) <-> ( ph \/_ ps ) ) )

  proof
    wph
    wps
    wnan
    wph
    wps
    wa
    #
    wn
    #
    wph
    wps
    wo
    #
    wph
    wps
    wxo
    #
    wb
    #
    wph
    wps
    df-nan
    @1
    @4
    @3
    @2
    @1
    wph
    wps
    xor2
    #
    rbaibr
    @4
    @2
    @2
    @1
    wa
    #
    wb
    #
    @1
    @3
    @6
    @2
    @5
    bibi2i
    @7
    @2
    @1
    wi
    @1
    @2
    @1
    pm4.71
    @2
    @1
    @1
    @0
    @2
    @0
    wph
    wps
    wph
    wps
    simpl
    orcd
    con3i
    @1
    id
    ja
    sylbir
    sylbi
    impbii
    bitri
end
