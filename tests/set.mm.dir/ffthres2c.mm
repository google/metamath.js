include "cful.mm"
include "co.mm"
include "wbr.mm"
include "cfth.mm"
include "wa.mm"
include "cin.mm"
include "fullres2c.mm"
include "fthres2c.mm"
include "anbi12d.mm"
include "brin.mm"
include "3bitr4g.mm"

theorem ffthres2c
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume ffthres2c.a: |- A = ( Base ` C )
  assume ffthres2c.e: |- E = ( D |`s S )
  assume ffthres2c.d: |- ( ph -> D e. Cat )
  assume ffthres2c.r: |- ( ph -> S e. V )
  assume ffthres2c.1: |- ( ph -> F : A --> S )


  assert |- ( ph -> ( F ( ( C Full D ) i^i ( C Faith D ) ) G <-> F ( ( C Full E ) i^i ( C Faith E ) ) G ) )

  proof
    wph
    cF
    cG
    cC
    cD
    cful
    co
    #
    wbr
    #
    cF
    cG
    cC
    cD
    cfth
    co
    #
    wbr
    #
    wa
    cF
    cG
    cC
    cE
    cful
    co
    #
    wbr
    #
    cF
    cG
    cC
    cE
    cfth
    co
    #
    wbr
    #
    wa
    cF
    cG
    @0
    @2
    cin
    wbr
    cF
    cG
    @4
    @6
    cin
    wbr
    wph
    @1
    @5
    @3
    @7
    wph
    cA
    cC
    cD
    cS
    cE
    cF
    cG
    cV
    ffthres2c.a
    ffthres2c.e
    ffthres2c.d
    ffthres2c.r
    ffthres2c.1
    fullres2c
    wph
    cA
    cC
    cD
    cS
    cE
    cF
    cG
    cV
    ffthres2c.a
    ffthres2c.e
    ffthres2c.d
    ffthres2c.r
    ffthres2c.1
    fthres2c
    anbi12d
    cF
    cG
    @0
    @2
    brin
    cF
    cG
    @4
    @6
    brin
    3bitr4g
end
