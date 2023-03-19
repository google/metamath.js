include "cvv.mm"
include "wcel.mm"
include "cn0.mm"
include "crelexp.mm"
include "co.mm"
include "cuni.mm"
include "wss.mm"
include "relexpfld.mm"
include "ex.mm"
include "syl5com.mm"

theorem relexpfldd
  let wph: wff ph
  let cR: class R
  let cN: class N
  assume relexpfldd.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( N e. NN0 -> U. U. ( R ^r N ) C_ U. U. R ) )

  proof
    wph
    cR
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cR
    cN
    crelexp
    co
    cuni
    cuni
    cR
    cuni
    cuni
    wss
    #
    relexpfldd.2
    @1
    @0
    @2
    cR
    cN
    cvv
    relexpfld
    ex
    syl5com
end
