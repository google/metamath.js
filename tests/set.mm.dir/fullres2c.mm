include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "crn.mm"
include "cfv.mm"
include "chom.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cful.mm"
include "funcres2c.mm"
include "wcel.mm"
include "eqid.mm"
include "resshom.mm"
include "syl.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "isfull.mm"
include "3bitr4g.mm"

theorem fullres2c
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


  assert |- ( ph -> ( F ( C Full D ) G <-> F ( C Full E ) G ) )

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
    #
    vy
    cv
    #
    cG
    co
    crn
    #
    @1
    cF
    cfv
    #
    @2
    cF
    cfv
    #
    cD
    chom
    cfv
    #
    co
    #
    wceq
    #
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
    @3
    @4
    @5
    cE
    chom
    cfv
    #
    co
    #
    wceq
    #
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
    cD
    cful
    co
    wbr
    cF
    cG
    cC
    cE
    cful
    co
    wbr
    wph
    @0
    @10
    @9
    @14
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
    funcres2c
    wph
    @8
    @13
    vx
    vy
    cA
    cA
    wph
    @7
    @12
    @3
    wph
    @6
    @11
    @4
    @5
    wph
    cS
    cV
    wcel
    @6
    @11
    wceq
    ffthres2c.r
    cS
    cD
    cE
    @6
    cV
    ffthres2c.e
    @6
    eqid
    #
    resshom
    syl
    oveqd
    eqeq2d
    2ralbidv
    anbi12d
    vx
    vy
    cA
    cC
    cD
    cF
    cG
    @6
    ffthres2c.a
    @15
    isfull
    vx
    vy
    cA
    cC
    cE
    cF
    cG
    @11
    ffthres2c.a
    @11
    eqid
    isfull
    3bitr4g
end
