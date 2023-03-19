include "crn.mm"
include "wss.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfrn.mm"
include "nfcv.mm"
include "nfss.mm"
include "nfan.mm"
include "cv.mm"
include "simplr.mm"
include "simpr.mm"
include "adantlr.mm"
include "elrnmpt1d.mm"
include "sseldd.mm"
include "ralrimia.mm"
include "rnmptss.mm"
include "adantl.mm"
include "impbida.mm"

theorem rnmptssbi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  assume rnmptssbi.1: |- F/ x ph
  assume rnmptssbi.2: |- F = ( x e. A |-> B )
  assume rnmptssbi.3: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint A x
  disjoint C x
  assert |- ( ph -> ( ran F C_ C <-> A. x e. A B e. C ) )

  proof
    wph
    cF
    crn
    #
    cC
    wss
    #
    cB
    cC
    wcel
    #
    vx
    cA
    wral
    #
    wph
    @1
    wa
    #
    @2
    vx
    cA
    wph
    @1
    vx
    rnmptssbi.1
    vx
    @0
    cC
    vx
    cF
    vx
    cF
    vx
    cA
    cB
    cmpt
    rnmptssbi.2
    vx
    cA
    cB
    nfmpt1
    nfcxfr
    nfrn
    vx
    cC
    nfcv
    nfss
    nfan
    @4
    vx
    cv
    cA
    wcel
    #
    wa
    #
    @0
    cC
    cB
    wph
    @1
    @5
    simplr
    @6
    vx
    cA
    cB
    cF
    cV
    rnmptssbi.2
    @4
    @5
    simpr
    wph
    @5
    cB
    cV
    wcel
    @1
    rnmptssbi.3
    adantlr
    elrnmpt1d
    sseldd
    ralrimia
    @3
    @1
    wph
    vx
    cA
    cB
    cC
    cF
    rnmptssbi.2
    rnmptss
    adantl
    impbida
end
