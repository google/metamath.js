include "wb.mm"
include "wi.mm"
include "wa.mm"
include "wn.mm"
include "wif.mm"
include "dfbi2.mm"
include "wtru.mm"
include "ifpim1.mm"
include "ifpn.mm"
include "bitr4i.mm"
include "ifpim2.mm"
include "anbi12i.mm"
include "ifpan23.mm"
include "ancom.mm"
include "truan.mm"
include "bitri.mm"
include "ifpbi23.mm"
include "mp2an.mm"

theorem ifpdfbi
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> if- ( ph , ps , -. ps ) )

  proof
    wph
    wps
    wb
    wph
    wps
    wi
    #
    wps
    wph
    wi
    #
    wa
    #
    wph
    wps
    wps
    wn
    #
    wif
    #
    wph
    wps
    dfbi2
    @2
    wph
    wps
    wtru
    wif
    #
    wph
    wtru
    @3
    wif
    #
    wa
    #
    @4
    @0
    @5
    @1
    @6
    @0
    wph
    wn
    wtru
    wps
    wif
    @5
    wph
    wps
    ifpim1
    wph
    wps
    wtru
    ifpn
    bitr4i
    wps
    wph
    ifpim2
    anbi12i
    @7
    wph
    wps
    wtru
    wa
    #
    wtru
    @3
    wa
    #
    wif
    #
    @4
    wph
    wps
    wtru
    wtru
    @3
    ifpan23
    @8
    wps
    wb
    @9
    @3
    wb
    @10
    @4
    wb
    @8
    wtru
    wps
    wa
    wps
    wps
    wtru
    ancom
    wps
    truan
    bitri
    @3
    truan
    @8
    wps
    @9
    @3
    wph
    ifpbi23
    mp2an
    bitri
    bitri
    bitri
end
