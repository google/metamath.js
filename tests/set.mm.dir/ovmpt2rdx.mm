include "nfv.mm"
include "nfcv.mm"
include "ovmpt2rdxf.mm"

theorem ovmpt2rdx
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
  let vk: setvar k
  assume ovmpt2rdx.1: |- ( ph -> F = ( x e. C , y e. D |-> R ) )
  assume ovmpt2rdx.2: |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S )
  assume ovmpt2rdx.3: |- ( ( ph /\ y = B ) -> C = L )
  assume ovmpt2rdx.4: |- ( ph -> A e. L )
  assume ovmpt2rdx.5: |- ( ph -> B e. D )
  assume ovmpt2rdx.6: |- ( ph -> S e. X )

  disjoint x y
  disjoint A x
  disjoint B y
  disjoint A y
  disjoint B x
  disjoint S x
  disjoint S y
  disjoint ph x
  disjoint ph y
  disjoint k x
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
    ovmpt2rdx.1
    ovmpt2rdx.2
    ovmpt2rdx.3
    ovmpt2rdx.4
    ovmpt2rdx.5
    ovmpt2rdx.6
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
    ovmpt2rdxf
end
