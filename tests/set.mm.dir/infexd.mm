include "cinf.mm"
include "ccnv.mm"
include "csup.mm"
include "cvv.mm"
include "df-inf.mm"
include "wor.mm"
include "cnvso.mm"
include "sylib.mm"
include "supexd.mm"
include "syl5eqel.mm"

theorem infexd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  assume infexd.1: |- ( ph -> R Or A )


  assert |- ( ph -> inf ( B , A , R ) e. _V )

  proof
    wph
    cB
    cA
    cR
    cinf
    cB
    cA
    cR
    ccnv
    #
    csup
    cvv
    cB
    cA
    cR
    df-inf
    wph
    cA
    cB
    @0
    wph
    cA
    cR
    wor
    cA
    @0
    wor
    infexd.1
    cA
    cR
    cnvso
    sylib
    supexd
    syl5eqel
end
