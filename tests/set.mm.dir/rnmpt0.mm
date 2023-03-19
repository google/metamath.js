include "c0.mm"
include "wceq.mm"
include "cmpt.mm"
include "cdm.mm"
include "crn.mm"
include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "ex.mm"
include "ralrimi.mm"
include "dmmptg.mm"
include "syl.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "wb.mm"
include "dm0rn0.mm"
include "a1i.mm"
include "rneqi.mm"
include "3bitrrd.mm"

theorem rnmpt0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  assume rnmpt0.1: |- F/ x ph
  assume rnmpt0.2: |- ( ( ph /\ x e. A ) -> B e. V )
  assume rnmpt0.3: |- F = ( x e. A |-> B )

  disjoint A x
  assert |- ( ph -> ( ran F = (/) <-> A = (/) ) )

  proof
    wph
    cA
    c0
    wceq
    vx
    cA
    cB
    cmpt
    #
    cdm
    #
    c0
    wceq
    #
    @0
    crn
    #
    c0
    wceq
    #
    cF
    crn
    #
    c0
    wceq
    wph
    cA
    @1
    c0
    wph
    @1
    cA
    wph
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    @1
    cA
    wceq
    wph
    @6
    vx
    cA
    rnmpt0.1
    wph
    vx
    cv
    cA
    wcel
    @6
    rnmpt0.2
    ex
    ralrimi
    vx
    cA
    cB
    cV
    dmmptg
    syl
    eqcomd
    eqeq1d
    @2
    @4
    wb
    wph
    @0
    dm0rn0
    a1i
    wph
    @3
    @5
    c0
    wph
    @5
    @3
    @5
    @3
    wceq
    wph
    cF
    @0
    rnmpt0.3
    rneqi
    a1i
    eqcomd
    eqeq1d
    3bitrrd
end
