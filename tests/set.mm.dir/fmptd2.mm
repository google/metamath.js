include "nfv.mm"
include "fmptd2f.mm"

theorem fmptd2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume fmptd2.1: |- ( ( ph /\ x e. A ) -> B e. C )

  disjoint A x
  disjoint C x
  disjoint ph x
  assert |- ( ph -> ( x e. A |-> B ) : A --> C )

  proof
    wph
    vx
    cA
    cB
    cC
    wph
    vx
    nfv
    fmptd2.1
    fmptd2f
end
