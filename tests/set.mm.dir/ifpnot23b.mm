include "wn.mm"
include "wif.mm"
include "ifpnot23.mm"
include "wb.mm"
include "notnotb.mm"
include "ifpbi2.mm"
include "ax-mp.mm"
include "bitr4i.mm"

theorem ifpnot23b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. if- ( ph , -. ps , ch ) <-> if- ( ph , ps , -. ch ) )

  proof
    wph
    wps
    wn
    #
    wch
    wif
    wn
    wph
    @0
    wn
    #
    wch
    wn
    #
    wif
    #
    wph
    wps
    @2
    wif
    #
    wph
    @0
    wch
    ifpnot23
    wps
    @1
    wb
    @4
    @3
    wb
    wps
    notnotb
    wps
    @1
    wph
    @2
    ifpbi2
    ax-mp
    bitr4i
end
