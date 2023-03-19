include "cres.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "fssresd.mm"
include "feqmptd.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "syl6eq.mm"

theorem feqresmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume feqmptd.1: |- ( ph -> F : A --> B )
  assume feqresmpt.2: |- ( ph -> C C_ A )

  disjoint A x
  disjoint C x
  disjoint F x
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
    wph
    cA
    cB
    cC
    cF
    feqmptd.1
    feqresmpt.2
    fssresd
    feqmptd
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
