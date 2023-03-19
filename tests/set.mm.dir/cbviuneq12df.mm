include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wss.mm"
include "eqimss.mm"
include "syl.mm"
include "ss2iundf.mm"
include "eqssd.mm"

theorem cbviuneq12df
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  assume cbviuneq12df.xph: |- F/ x ph
  assume cbviuneq12df.yph: |- F/ y ph
  assume cbviuneq12df.x: |- F/_ x X
  assume cbviuneq12df.y: |- F/_ y Y
  assume cbviuneq12df.xa: |- F/_ x A
  assume cbviuneq12df.ya: |- F/_ y A
  assume cbviuneq12df.b: |- F/_ y B
  assume cbviuneq12df.xc: |- F/_ x C
  assume cbviuneq12df.yc: |- F/_ y C
  assume cbviuneq12df.d: |- F/_ x D
  assume cbviuneq12df.f: |- F/_ x F
  assume cbviuneq12df.g: |- F/_ y G
  assume cbviuneq12df.xel: |- ( ( ph /\ y e. C ) -> X e. A )
  assume cbviuneq12df.yel: |- ( ( ph /\ x e. A ) -> Y e. C )
  assume cbviuneq12df.xsub: |- ( ( ph /\ y e. C /\ x = X ) -> B = F )
  assume cbviuneq12df.ysub: |- ( ( ph /\ x e. A /\ y = Y ) -> D = G )
  assume cbviuneq12df.eq1: |- ( ( ph /\ x e. A ) -> B = G )
  assume cbviuneq12df.eq2: |- ( ( ph /\ y e. C ) -> D = F )

  disjoint x y
  assert |- ( ph -> U_ x e. A B = U_ y e. C D )

  proof
    wph
    vx
    cA
    cB
    ciun
    vy
    cC
    cD
    ciun
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cG
    cY
    cbviuneq12df.xph
    cbviuneq12df.yph
    cbviuneq12df.y
    cbviuneq12df.ya
    cbviuneq12df.b
    cbviuneq12df.xc
    cbviuneq12df.yc
    cbviuneq12df.d
    cbviuneq12df.g
    cbviuneq12df.yel
    cbviuneq12df.ysub
    wph
    vx
    cv
    cA
    wcel
    wa
    cB
    cG
    wceq
    cB
    cG
    wss
    cbviuneq12df.eq1
    cB
    cG
    eqimss
    syl
    ss2iundf
    wph
    vy
    vx
    cC
    cD
    cA
    cB
    cF
    cX
    cbviuneq12df.yph
    cbviuneq12df.xph
    cbviuneq12df.x
    cbviuneq12df.xc
    cbviuneq12df.d
    cbviuneq12df.ya
    cbviuneq12df.xa
    cbviuneq12df.b
    cbviuneq12df.f
    cbviuneq12df.xel
    cbviuneq12df.xsub
    wph
    vy
    cv
    cC
    wcel
    wa
    cD
    cF
    wceq
    cD
    cF
    wss
    cbviuneq12df.eq2
    cD
    cF
    eqimss
    syl
    ss2iundf
    eqssd
end
