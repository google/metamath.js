include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "infxrcld.mm"

theorem infxrrnmptcl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume infxrrnmptcl.1: |- F/ x ph
  assume infxrrnmptcl.2: |- ( ( ph /\ x e. A ) -> B e. RR* )

  disjoint A x
  assert |- ( ph -> inf ( ran ( x e. A |-> B ) , RR* , < ) e. RR* )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    crn
    wph
    vx
    cA
    cB
    cxr
    @0
    infxrrnmptcl.1
    @0
    eqid
    infxrrnmptcl.2
    rnmptssd
    infxrcld
end
