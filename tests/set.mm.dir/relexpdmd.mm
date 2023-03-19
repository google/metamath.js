include "cvv.mm"
include "wcel.mm"
include "cn0.mm"
include "crelexp.mm"
include "co.mm"
include "cdm.mm"
include "cuni.mm"
include "wss.mm"
include "relexpdm.mm"
include "ex.mm"
include "syl5com.mm"

theorem relexpdmd
  let wph: wff ph
  let cR: class R
  let cN: class N
  assume relexpdmd.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( N e. NN0 -> dom ( R ^r N ) C_ U. U. R ) )

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
    cdm
    cR
    cuni
    cuni
    wss
    #
    relexpdmd.2
    @1
    @0
    @2
    cR
    cN
    cvv
    relexpdm
    ex
    syl5com
end
