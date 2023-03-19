include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "3ad2ant1.mm"
include "mpt2eq3dva.mm"

theorem mpt2eq3dv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mpt2eq3dv.1: |- ( ph -> C = D )

  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D ) )

  proof
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    wph
    vx
    cv
    cA
    wcel
    cC
    cD
    wceq
    vy
    cv
    cB
    wcel
    mpt2eq3dv.1
    3ad2ant1
    mpt2eq3dva
end
