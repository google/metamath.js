include "wnan.mm"
include "wa.mm"
include "wn.mm"
include "wfal.mm"
include "wif.mm"
include "wtru.mm"
include "df-nan.mm"
include "ifpdfan.mm"
include "notbii.mm"
include "ifpnot23.mm"
include "wb.mm"
include "notfal.mm"
include "ifpbi3.mm"
include "ax-mp.mm"
include "bitri.mm"
include "3bitri.mm"

theorem ifpdfnan
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -/\ ps ) <-> if- ( ph , -. ps , T. ) )

  proof
    wph
    wps
    wnan
    wph
    wps
    wa
    #
    wn
    wph
    wps
    wfal
    wif
    #
    wn
    #
    wph
    wps
    wn
    #
    wtru
    wif
    #
    wph
    wps
    df-nan
    @0
    @1
    wph
    wps
    ifpdfan
    notbii
    @2
    wph
    @3
    wfal
    wn
    #
    wif
    #
    @4
    wph
    wps
    wfal
    ifpnot23
    @5
    wtru
    wb
    @6
    @4
    wb
    notfal
    @5
    wtru
    wph
    @3
    ifpbi3
    ax-mp
    bitri
    3bitri
end
