include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "mpteq2dva.mm"

theorem mpteq2dv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume mpteq2dv.1: |- ( ph -> B = C )

  disjoint ph x
  assert |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) )

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
    mpteq2dv.1
    adantr
    mpteq2dva
end
