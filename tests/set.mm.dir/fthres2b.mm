include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "wa.mm"
include "cresc.mm"
include "cfth.mm"
include "funcres2b.mm"
include "anbi1d.mm"
include "isfth.mm"
include "3bitr4g.mm"

theorem fthres2b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cY: class Y
  assume fthres2b.a: |- A = ( Base ` C )
  assume fthres2b.h: |- H = ( Hom ` C )
  assume fthres2b.r: |- ( ph -> R e. ( Subcat ` D ) )
  assume fthres2b.s: |- ( ph -> R Fn ( S X. S ) )
  assume fthres2b.1: |- ( ph -> F : A --> S )
  assume fthres2b.2: |- ( ( ph /\ ( x e. A /\ y e. A ) ) -> ( x G y ) : Y --> ( ( F ` x ) R ( F ` y ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint R x
  disjoint R y
  assert |- ( ph -> ( F ( C Faith D ) G <-> F ( C Faith ( D |`cat R ) ) G ) )

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
    cD
    cR
    cresc
    co
    #
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
    @2
    cfth
    co
    wbr
    wph
    @0
    @3
    @1
    wph
    vx
    vy
    cA
    cC
    cD
    cR
    cS
    cF
    cG
    cH
    cY
    fthres2b.a
    fthres2b.h
    fthres2b.r
    fthres2b.s
    fthres2b.1
    fthres2b.2
    funcres2b
    anbi1d
    vx
    vy
    cA
    cC
    cD
    cF
    cG
    fthres2b.a
    isfth
    vx
    vy
    cA
    cC
    @2
    cF
    cG
    fthres2b.a
    isfth
    3bitr4g
end
