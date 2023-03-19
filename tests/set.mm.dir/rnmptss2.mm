include "cmpt.mm"
include "crn.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "eqid.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "sselda.mm"
include "elrnmpt1d.mm"
include "rnmptssdf.mm"

theorem rnmptss2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume rnmptss2.1: |- F/ x ph
  assume rnmptss2.3: |- ( ph -> A C_ B )
  assume rnmptss2.4: |- ( ( ph /\ x e. A ) -> C e. V )

  disjoint A x
  assert |- ( ph -> ran ( x e. A |-> C ) C_ ran ( x e. B |-> C ) )

  proof
    wph
    vx
    cA
    cC
    vx
    cB
    cC
    cmpt
    #
    crn
    vx
    cA
    cC
    cmpt
    #
    rnmptss2.1
    vx
    @0
    vx
    cB
    cC
    nfmpt1
    nfrn
    @1
    eqid
    wph
    vx
    cv
    #
    cA
    wcel
    wa
    vx
    cB
    cC
    @0
    cV
    @0
    eqid
    wph
    cA
    cB
    @2
    rnmptss2.3
    sselda
    rnmptss2.4
    elrnmpt1d
    rnmptssdf
end
