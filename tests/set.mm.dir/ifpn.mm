include "wi.mm"
include "wn.mm"
include "wa.mm"
include "wif.mm"
include "notnotb.mm"
include "imbi1i.mm"
include "anbi2ci.mm"
include "dfifp2.mm"
include "3bitr4i.mm"

theorem ifpn
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( if- ( ph , ps , ch ) <-> if- ( -. ph , ch , ps ) )

  proof
    wph
    wps
    wi
    #
    wph
    wn
    #
    wch
    wi
    #
    wa
    @2
    @1
    wn
    #
    wps
    wi
    #
    wa
    wph
    wps
    wch
    wif
    @1
    wch
    wps
    wif
    @0
    @4
    @2
    wph
    @3
    wps
    wph
    notnotb
    imbi1i
    anbi2ci
    wph
    wps
    wch
    dfifp2
    @1
    wch
    wps
    dfifp2
    3bitr4i
end
