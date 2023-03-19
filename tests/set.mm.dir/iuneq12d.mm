include "ciun.mm"
include "iuneq1d.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "iuneq2dv.mm"
include "eqtrd.mm"

theorem iuneq12d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume iuneq1d.1: |- ( ph -> A = B )
  assume iuneq12d.2: |- ( ph -> C = D )

  disjoint ph x
  disjoint A x
  disjoint B x
  assert |- ( ph -> U_ x e. A C = U_ x e. B D )

  proof
    wph
    vx
    cA
    cC
    ciun
    vx
    cB
    cC
    ciun
    vx
    cB
    cD
    ciun
    wph
    vx
    cA
    cB
    cC
    iuneq1d.1
    iuneq1d
    wph
    vx
    cB
    cC
    cD
    wph
    cC
    cD
    wceq
    vx
    cv
    cB
    wcel
    iuneq12d.2
    adantr
    iuneq2dv
    eqtrd
end
