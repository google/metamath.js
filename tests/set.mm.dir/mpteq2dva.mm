include "nfv.mm"
include "mpteq2da.mm"

theorem mpteq2dva
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume mpteq2dva.1: |- ( ( ph /\ x e. A ) -> B = C )

  disjoint ph x
  assert |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) )

  proof
    wph
    vx
    cA
    cB
    cC
    wph
    vx
    nfv
    mpteq2dva.1
    mpteq2da
end
