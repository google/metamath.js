include "wn.mm"
include "wa.mm"
include "wnan.mm"
include "wi.mm"
include "nannot.mm"
include "anbi12i.mm"
include "notbii.mm"
include "iman.mm"
include "df-nan.mm"
include "3bitr4i.mm"

theorem imnand2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> ps ) <-> ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) )

  proof
    wph
    wn
    #
    wps
    wn
    #
    wa
    #
    wn
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
    wn
    @0
    wps
    wi
    @3
    @4
    wnan
    @2
    @5
    @0
    @3
    @1
    @4
    wph
    nannot
    wps
    nannot
    anbi12i
    notbii
    @0
    wps
    iman
    @3
    @4
    df-nan
    3bitr4i
end
