include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "eqidd.mm"
include "ovmpt2dx.mm"

theorem ovmpt2d
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
  let cX: class X
  assume ovmpt2d.1: |- ( ph -> F = ( x e. C , y e. D |-> R ) )
  assume ovmpt2d.2: |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S )
  assume ovmpt2d.3: |- ( ph -> A e. C )
  assume ovmpt2d.4: |- ( ph -> B e. D )
  assume ovmpt2d.5: |- ( ph -> S e. X )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
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
    cD
    cX
    ovmpt2d.1
    ovmpt2d.2
    wph
    vx
    cv
    cA
    wceq
    wa
    cD
    eqidd
    ovmpt2d.3
    ovmpt2d.4
    ovmpt2d.5
    ovmpt2dx
end
