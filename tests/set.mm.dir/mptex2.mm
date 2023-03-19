include "wcel.mm"
include "cmpt.mm"
include "wf.mm"
include "wral.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"

theorem mptex2
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  assume mptex2.1: |- ( ph -> ( t e. A |-> B ) : A --> C )

  disjoint A t
  disjoint C t
  assert |- ( ( ph /\ t e. A ) -> B e. C )

  proof
    wph
    cB
    cC
    wcel
    #
    vt
    cA
    wph
    cA
    cC
    vt
    cA
    cB
    cmpt
    #
    wf
    @0
    vt
    cA
    wral
    mptex2.1
    vt
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
