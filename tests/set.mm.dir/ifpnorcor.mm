include "wif.mm"
include "wn.mm"
include "ifporcor.mm"
include "notbii.mm"
include "ifpnot23.mm"
include "3bitr3i.mm"

theorem ifpnorcor
  let wph: wff ph
  let wps: wff ps


  assert |- ( if- ( ph , -. ph , -. ps ) <-> if- ( ps , -. ps , -. ph ) )

  proof
    wph
    wph
    wps
    wif
    #
    wn
    wps
    wps
    wph
    wif
    #
    wn
    wph
    wph
    wn
    #
    wps
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
    ifporcor
    notbii
    wph
    wph
    wps
    ifpnot23
    wps
    wps
    wph
    ifpnot23
    3bitr3i
end
