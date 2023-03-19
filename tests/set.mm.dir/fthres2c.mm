include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "wa.mm"
include "cfth.mm"
include "funcres2c.mm"
include "anbi1d.mm"
include "isfth.mm"
include "3bitr4g.mm"

theorem fthres2c
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
  assume fthres2c.a: |- A = ( Base ` C )
  assume fthres2c.e: |- E = ( D |`s S )
  assume fthres2c.d: |- ( ph -> D e. Cat )
  assume fthres2c.r: |- ( ph -> S e. V )
  assume fthres2c.1: |- ( ph -> F : A --> S )


  assert |- ( ph -> ( F ( C Faith D ) G <-> F ( C Faith E ) G ) )

  proof
    wph
    cF
    cG
    cC
    cD
    cfunc
    co
    wbr
    #
    vx
    cv
    vy
    cv
    cG
    co
    ccnv
    wfun
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    cF
    cG
    cC
    cE
    cfunc
    co
    wbr
    #
    @1
    wa
    cF
    cG
    cC
    cD
    cfth
    co
    wbr
    cF
    cG
    cC
    cE
    cfth
    co
    wbr
    wph
    @0
    @2
    @1
    wph
    cA
    cC
    cD
    cS
    cE
    cF
    cG
    cV
    fthres2c.a
    fthres2c.e
    fthres2c.d
    fthres2c.r
    fthres2c.1
    funcres2c
    anbi1d
    vx
    vy
    cA
    cC
    cD
    cF
    cG
    fthres2c.a
    isfth
    vx
    vy
    cA
    cC
    cE
    cF
    cG
    fthres2c.a
    isfth
    3bitr4g
end
