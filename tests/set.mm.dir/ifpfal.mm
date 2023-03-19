include "wif.mm"
include "wn.mm"
include "ifpn.mm"
include "ifptru.mm"
include "syl5bb.mm"

theorem ifpfal
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ph -> ( if- ( ph , ps , ch ) <-> ch ) )

  proof
    wph
    wps
    wch
    wif
    wph
    wn
    #
    wch
    wps
    wif
    @0
    wch
    wph
    wps
    wch
    ifpn
    @0
    wch
    wps
    ifptru
    syl5bb
end
