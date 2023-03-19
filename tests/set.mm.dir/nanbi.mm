include "wb.mm"
include "wnan.mm"
include "wa.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "dfbi3.mm"
include "df-or.mm"
include "df-nan.mm"
include "bicomi.mm"
include "nannot.mm"
include "anbi12i.mm"
include "imbi12i.mm"
include "3bitri.mm"
include "nannan.mm"
include "bitr4i.mm"

theorem nanbi
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) )

  proof
    wph
    wps
    wb
    #
    wph
    wps
    wnan
    #
    wph
    wph
    wnan
    #
    wps
    wps
    wnan
    #
    wa
    #
    wi
    #
    @1
    @2
    @3
    wnan
    wnan
    @0
    wph
    wps
    wa
    #
    wph
    wn
    #
    wps
    wn
    #
    wa
    #
    wo
    @6
    wn
    #
    @9
    wi
    @5
    wph
    wps
    dfbi3
    @6
    @9
    df-or
    @10
    @1
    @9
    @4
    @1
    @10
    wph
    wps
    df-nan
    bicomi
    @7
    @2
    @8
    @3
    wph
    nannot
    wps
    nannot
    anbi12i
    imbi12i
    3bitri
    @1
    @3
    @2
    nannan
    bitr4i
end
