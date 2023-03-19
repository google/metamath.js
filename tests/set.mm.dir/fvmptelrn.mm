include "wcel.mm"
include "cmpt.mm"
include "wf.mm"
include "wral.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"

theorem fvmptelrn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume fvmptelrn.1: |- ( ph -> ( x e. A |-> B ) : A --> C )

  disjoint A x
  disjoint C x
  assert |- ( ( ph /\ x e. A ) -> B e. C )

  proof
    wph
    cB
    cC
    wcel
    #
    vx
    cA
    wph
    cA
    cC
    vx
    cA
    cB
    cmpt
    #
    wf
    @0
    vx
    cA
    wral
    fvmptelrn.1
    vx
    cA
    cC
    cB
    @1
    @1
    eqid
    fmpt
    sylibr
    r19.21bi
end
