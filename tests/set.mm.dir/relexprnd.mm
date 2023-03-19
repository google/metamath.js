include "cvv.mm"
include "wcel.mm"
include "cn0.mm"
include "crelexp.mm"
include "co.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "relexprn.mm"
include "ex.mm"
include "syl5com.mm"

theorem relexprnd
  let wph: wff ph
  let cR: class R
  let cN: class N
  assume relexprnd.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( N e. NN0 -> ran ( R ^r N ) C_ U. U. R ) )

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
    crn
    cR
    cuni
    cuni
    wss
    #
    relexprnd.2
    @1
    @0
    @2
    cR
    cN
    cvv
    relexprn
    ex
    syl5com
end
