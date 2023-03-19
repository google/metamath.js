include "wn.mm"
include "wif.mm"
include "ifpbicor.mm"
include "wb.mm"
include "notnotb.mm"
include "ifpbi3.mm"
include "ax-mp.mm"
include "ifpn.mm"
include "3bitr4i.mm"

theorem ifpxorcor
  let wph: wff ph
  let wps: wff ps


  assert |- ( if- ( ph , -. ps , ps ) <-> if- ( ps , -. ph , ph ) )

  proof
    wph
    wps
    wn
    #
    @0
    wn
    #
    wif
    #
    @0
    wph
    wph
    wn
    #
    wif
    wph
    @0
    wps
    wif
    #
    wps
    @3
    wph
    wif
    wph
    @0
    ifpbicor
    wps
    @1
    wb
    @4
    @2
    wb
    wps
    notnotb
    wps
    @1
    wph
    @0
    ifpbi3
    ax-mp
    wps
    @3
    wph
    ifpn
    3bitr4i
end
