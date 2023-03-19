include "cful.mm"
include "co.mm"
include "cfth.mm"
include "ccofu.mm"
include "cin.mm"
include "inss1.mm"
include "sseldi.mm"
include "cofull.mm"
include "inss2.mm"
include "cofth.mm"
include "elind.mm"

theorem coffth
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  assume coffth.f: |- ( ph -> F e. ( ( C Full D ) i^i ( C Faith D ) ) )
  assume coffth.g: |- ( ph -> G e. ( ( D Full E ) i^i ( D Faith E ) ) )


  assert |- ( ph -> ( G o.func F ) e. ( ( C Full E ) i^i ( C Faith E ) ) )

  proof
    wph
    cC
    cE
    cful
    co
    cC
    cE
    cfth
    co
    cG
    cF
    ccofu
    co
    wph
    cC
    cD
    cE
    cF
    cG
    wph
    cC
    cD
    cful
    co
    #
    cC
    cD
    cfth
    co
    #
    cin
    #
    @0
    cF
    @0
    @1
    inss1
    coffth.f
    sseldi
    wph
    cD
    cE
    cful
    co
    #
    cD
    cE
    cfth
    co
    #
    cin
    #
    @3
    cG
    @3
    @4
    inss1
    coffth.g
    sseldi
    cofull
    wph
    cC
    cD
    cE
    cF
    cG
    wph
    @2
    @1
    cF
    @0
    @1
    inss2
    coffth.f
    sseldi
    wph
    @5
    @4
    cG
    @3
    @4
    inss2
    coffth.g
    sseldi
    cofth
    elind
end
