include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "iuneq2dv.mm"

theorem iuneq2d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iuneq2d.2: |- ( ph -> B = C )

  disjoint ph x
  disjoint A x
  assert |- ( ph -> U_ x e. A B = U_ x e. A C )

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
    iuneq2d.2
    adantr
    iuneq2dv
end
