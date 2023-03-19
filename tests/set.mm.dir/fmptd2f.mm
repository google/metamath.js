include "cmpt.mm"
include "eqid.mm"
include "fmptdf.mm"

theorem fmptd2f
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume fmptd2f.1: |- F/ x ph
  assume fmptd2f.2: |- ( ( ph /\ x e. A ) -> B e. C )

  disjoint A x
  disjoint C x
  assert |- ( ph -> ( x e. A |-> B ) : A --> C )

  proof
    wph
    vx
    cA
    cB
    cC
    vx
    cA
    cB
    cmpt
    #
    fmptd2f.1
    fmptd2f.2
    @0
    eqid
    fmptdf
end
