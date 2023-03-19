include "wn.mm"
include "wif.mm"
include "ifpnot23.mm"
include "wb.mm"
include "notnotb.mm"
include "ifpbi3.mm"
include "ax-mp.mm"
include "bitr4i.mm"

theorem ifpnot23c
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. if- ( ph , ps , -. ch ) <-> if- ( ph , -. ps , ch ) )

  proof
    wph
    wps
    wch
    wn
    #
    wif
    wn
    wph
    wps
    wn
    #
    @0
    wn
    #
    wif
    #
    wph
    @1
    wch
    wif
    #
    wph
    wps
    @0
    ifpnot23
    wch
    @2
    wb
    @4
    @3
    wb
    wch
    notnotb
    wch
    @2
    wph
    @1
    ifpbi3
    ax-mp
    bitr4i
end
