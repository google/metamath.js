include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "wa.mm"
include "mpt2eq123dva.mm"

theorem mpt2eq123dv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let vz: setvar z
  assume mpt2eq123dv.1: |- ( ph -> A = D )
  assume mpt2eq123dv.2: |- ( ph -> B = E )
  assume mpt2eq123dv.3: |- ( ph -> C = F )

  disjoint ph x
  disjoint ph y
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint E z
  disjoint x z
  disjoint ph z
  disjoint F z
  disjoint y z
  assert |- ( ph -> ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) )

  proof
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cE
    cF
    mpt2eq123dv.1
    wph
    cB
    cE
    wceq
    vx
    cv
    cA
    wcel
    #
    mpt2eq123dv.2
    adantr
    wph
    cC
    cF
    wceq
    @0
    vy
    cv
    cB
    wcel
    wa
    mpt2eq123dv.3
    adantr
    mpt2eq123dva
end
