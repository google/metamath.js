include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "c1stc.mm"
include "met1stc.mm"
include "syl.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "1stccn.mm"

theorem metcn4
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let vf: setvar f
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let cP: class P
  assume metcnp4.3: |- J = ( MetOpen ` C )
  assume metcnp4.4: |- K = ( MetOpen ` D )
  assume metcnp4.5: |- ( ph -> C e. ( *Met ` X ) )
  assume metcnp4.6: |- ( ph -> D e. ( *Met ` Y ) )
  assume metcn4.7: |- ( ph -> F : X --> Y )

  disjoint f x
  disjoint C f
  disjoint C x
  disjoint D f
  disjoint D x
  disjoint F f
  disjoint F x
  disjoint J f
  disjoint J x
  disjoint f ph
  disjoint ph x
  disjoint X f
  disjoint X x
  disjoint Y f
  disjoint Y x
  disjoint K f
  disjoint K x
  disjoint P f
  disjoint P x
  assert |- ( ph -> ( F e. ( J Cn K ) <-> A. f ( f : NN --> X -> A. x ( f ( ~~>t ` J ) x -> ( F o. f ) ( ~~>t ` K ) ( F ` x ) ) ) ) )

  proof
    wph
    vx
    vf
    cF
    cJ
    cK
    cX
    cY
    wph
    cC
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    c1stc
    wcel
    metcnp4.5
    cC
    cJ
    cX
    metcnp4.3
    met1stc
    syl
    wph
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    metcnp4.5
    cC
    cJ
    cX
    metcnp4.3
    mopntopon
    syl
    wph
    cD
    cY
    cxmt
    cfv
    wcel
    cK
    cY
    ctopon
    cfv
    wcel
    metcnp4.6
    cD
    cK
    cY
    metcnp4.4
    mopntopon
    syl
    metcn4.7
    1stccn
end
