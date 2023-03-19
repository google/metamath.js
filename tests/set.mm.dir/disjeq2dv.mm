include "wceq.mm"
include "wral.mm"
include "wdisj.mm"
include "wb.mm"
include "ralrimiva.mm"
include "disjeq2.mm"
include "syl.mm"

theorem disjeq2dv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume disjeq2dv.1: |- ( ( ph /\ x e. A ) -> B = C )

  disjoint ph x
  assert |- ( ph -> ( Disj_ x e. A B <-> Disj_ x e. A C ) )

  proof
    wph
    cB
    cC
    wceq
    #
    vx
    cA
    wral
    vx
    cA
    cB
    wdisj
    vx
    cA
    cC
    wdisj
    wb
    wph
    @0
    vx
    cA
    disjeq2dv.1
    ralrimiva
    vx
    cA
    cB
    cC
    disjeq2
    syl
end
