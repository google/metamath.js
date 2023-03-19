include "cres.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfres.mm"
include "fssresd.mm"
include "feqmptdf.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "syl6eq.mm"

theorem feqresmptf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume feqresmptf.1: |- F/_ x F
  assume feqresmptf.2: |- ( ph -> F : A --> B )
  assume feqresmptf.3: |- ( ph -> C C_ A )

  disjoint C x
  assert |- ( ph -> ( F |` C ) = ( x e. C |-> ( F ` x ) ) )

  proof
    wph
    cF
    cC
    cres
    #
    vx
    cC
    vx
    cv
    #
    @0
    cfv
    #
    cmpt
    vx
    cC
    @1
    cF
    cfv
    #
    cmpt
    wph
    vx
    cC
    cB
    @0
    vx
    cC
    nfcv
    #
    vx
    cF
    cC
    feqresmptf.1
    @4
    nfres
    wph
    cA
    cB
    cC
    cF
    feqresmptf.2
    feqresmptf.3
    fssresd
    feqmptdf
    vx
    cC
    @2
    @3
    @1
    cC
    cF
    fvres
    mpteq2ia
    syl6eq
end
