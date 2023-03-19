include "wn.mm"
include "wif.mm"
include "ifpnot23.mm"
include "wb.mm"
include "notnotb.mm"
include "ifpbi23.mm"
include "mp2an.mm"
include "bitr4i.mm"

theorem ifpnot23d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. if- ( ph , -. ps , -. ch ) <-> if- ( ph , ps , ch ) )

  proof
    wph
    wps
    wn
    #
    wch
    wn
    #
    wif
    wn
    wph
    @0
    wn
    #
    @1
    wn
    #
    wif
    #
    wph
    wps
    wch
    wif
    #
    wph
    @0
    @1
    ifpnot23
    wps
    @2
    wb
    wch
    @3
    wb
    @5
    @4
    wb
    wps
    notnotb
    wch
    notnotb
    wps
    @2
    wch
    @3
    wph
    ifpbi23
    mp2an
    bitr4i
end
