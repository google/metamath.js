include "nfv.mm"
include "nfcv.mm"
include "cbviuneq12df.mm"

theorem cbviuneq12dv
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
  assume cbviuneq12dv.xel: |- ( ( ph /\ y e. C ) -> X e. A )
  assume cbviuneq12dv.yel: |- ( ( ph /\ x e. A ) -> Y e. C )
  assume cbviuneq12dv.xsub: |- ( ( ph /\ y e. C /\ x = X ) -> B = F )
  assume cbviuneq12dv.ysub: |- ( ( ph /\ x e. A /\ y = Y ) -> D = G )
  assume cbviuneq12dv.eq1: |- ( ( ph /\ x e. A ) -> B = G )
  assume cbviuneq12dv.eq2: |- ( ( ph /\ y e. C ) -> D = F )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint F x
  disjoint G y
  disjoint X x
  disjoint Y y
  assert |- ( ph -> U_ x e. A B = U_ y e. C D )

  proof
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cF
    cG
    cX
    cY
    wph
    vx
    nfv
    wph
    vy
    nfv
    vx
    cX
    nfcv
    vy
    cY
    nfcv
    vx
    cA
    nfcv
    vy
    cA
    nfcv
    vy
    cB
    nfcv
    vx
    cC
    nfcv
    vy
    cC
    nfcv
    vx
    cD
    nfcv
    vx
    cF
    nfcv
    vy
    cG
    nfcv
    cbviuneq12dv.xel
    cbviuneq12dv.yel
    cbviuneq12dv.xsub
    cbviuneq12dv.ysub
    cbviuneq12dv.eq1
    cbviuneq12dv.eq2
    cbviuneq12df
end
