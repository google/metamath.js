include "wif.mm"
include "wn.mm"
include "ifpancor.mm"
include "notbii.mm"
include "ifpnot23.mm"
include "3bitr3i.mm"

theorem ifpnancor
  let wph: wff ph
  let wps: wff ps


  assert |- ( if- ( ph , -. ps , -. ph ) <-> if- ( ps , -. ph , -. ps ) )

  proof
    wph
    wps
    wph
    wif
    #
    wn
    wps
    wph
    wps
    wif
    #
    wn
    wph
    wps
    wn
    #
    wph
    wn
    #
    wif
    wps
    @3
    @2
    wif
    @0
    @1
    wph
    wps
    ifpancor
    notbii
    wph
    wps
    wph
    ifpnot23
    wps
    wph
    wps
    ifpnot23
    3bitr3i
end
