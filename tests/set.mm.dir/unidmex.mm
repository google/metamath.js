include "cdm.mm"
include "cuni.mm"
include "cvv.mm"
include "wcel.mm"
include "dmexg.mm"
include "uniexg.mm"
include "3syl.mm"
include "syl5eqel.mm"

theorem unidmex
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cX: class X
  assume unidmex.f: |- ( ph -> F e. V )
  assume unidmex.x: |- X = U. dom F


  assert |- ( ph -> X e. _V )

  proof
    wph
    cX
    cF
    cdm
    #
    cuni
    #
    cvv
    unidmex.x
    wph
    cF
    cV
    wcel
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    unidmex.f
    cF
    cV
    dmexg
    @0
    cvv
    uniexg
    3syl
    syl5eqel
end
