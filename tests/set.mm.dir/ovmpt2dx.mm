include "nfv.mm"
include "nfcv.mm"
include "ovmpt2dxf.mm"

theorem ovmpt2dx
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cL: class L
  let cX: class X
  assume ovmpt2dx.1: |- ( ph -> F = ( x e. C , y e. D |-> R ) )
  assume ovmpt2dx.2: |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S )
  assume ovmpt2dx.3: |- ( ( ph /\ x = A ) -> D = L )
  assume ovmpt2dx.4: |- ( ph -> A e. C )
  assume ovmpt2dx.5: |- ( ph -> B e. L )
  assume ovmpt2dx.6: |- ( ph -> S e. X )

  disjoint x y
  disjoint A x
  disjoint B y
  disjoint A y
  disjoint B x
  disjoint S x
  disjoint S y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( A F B ) = S )

  proof
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    cS
    cF
    cL
    cX
    ovmpt2dx.1
    ovmpt2dx.2
    ovmpt2dx.3
    ovmpt2dx.4
    ovmpt2dx.5
    ovmpt2dx.6
    wph
    vx
    nfv
    wph
    vy
    nfv
    vy
    cA
    nfcv
    vx
    cB
    nfcv
    vx
    cS
    nfcv
    vy
    cS
    nfcv
    ovmpt2dxf
end
