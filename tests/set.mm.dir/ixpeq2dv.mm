include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "ixpeq2dva.mm"

theorem ixpeq2dv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume ixpeq2dv.1: |- ( ph -> B = C )

  disjoint ph x
  assert |- ( ph -> X_ x e. A B = X_ x e. A C )

  proof
    wph
    vx
    cA
    cB
    cC
    wph
    cB
    cC
    wceq
    vx
    cv
    cA
    wcel
    ixpeq2dv.1
    adantr
    ixpeq2dva
end
