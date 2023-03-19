include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "c1stc.mm"
include "met1stc.mm"
include "syl.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "1stccnp.mm"

theorem metcnp4
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume metcnp4.3: |- J = ( MetOpen ` C )
  assume metcnp4.4: |- K = ( MetOpen ` D )
  assume metcnp4.5: |- ( ph -> C e. ( *Met ` X ) )
  assume metcnp4.6: |- ( ph -> D e. ( *Met ` Y ) )
  assume metcnp4.7: |- ( ph -> P e. X )

  disjoint C f
  disjoint D f
  disjoint F f
  disjoint P f
  disjoint J f
  disjoint f ph
  disjoint X f
  disjoint Y f
  disjoint K f
  disjoint f x
  disjoint C x
  disjoint D x
  disjoint F x
  disjoint P x
  disjoint J x
  disjoint ph x
  disjoint X x
  disjoint Y x
  disjoint K x
  assert |- ( ph -> ( F e. ( ( J CnP K ) ` P ) <-> ( F : X --> Y /\ A. f ( ( f : NN --> X /\ f ( ~~>t ` J ) P ) -> ( F o. f ) ( ~~>t ` K ) ( F ` P ) ) ) ) )

  proof
    wph
    cP
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
    metcnp4.7
    1stccnp
end
