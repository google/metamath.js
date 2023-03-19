include "wn.mm"
include "wif.mm"
include "ifpbiidcor.mm"
include "ifpnot23b.mm"
include "mpbir.mm"

theorem ifpbiidcor2
  let wph: wff ph


  assert |- -. if- ( ph , -. ph , ph )

  proof
    wph
    wph
    wn
    #
    wph
    wif
    wn
    wph
    wph
    @0
    wif
    wph
    ifpbiidcor
    wph
    wph
    wph
    ifpnot23b
    mpbir
end
