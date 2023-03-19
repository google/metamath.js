include "nfv.mm"
include "nfcv.mm"
include "ss2iundf.mm"

theorem ss2iundv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let cY: class Y
  assume ss2iundv.el: |- ( ( ph /\ x e. A ) -> Y e. C )
  assume ss2iundv.sub: |- ( ( ph /\ x e. A /\ y = Y ) -> D = G )
  assume ss2iundv.ss: |- ( ( ph /\ x e. A ) -> B C_ G )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint G y
  disjoint Y y
  assert |- ( ph -> U_ x e. A B C_ U_ y e. C D )

  proof
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cG
    cY
    wph
    vx
    nfv
    wph
    vy
    nfv
    vy
    cY
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
    vy
    cG
    nfcv
    ss2iundv.el
    ss2iundv.sub
    ss2iundv.ss
    ss2iundf
end
