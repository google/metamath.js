include "wcel.mm"
include "cfv.mm"
include "cec.mm"
include "wceq.mm"
include "cvv.mm"
include "ecss.mm"
include "ssexd.mm"
include "cv.mm"
include "eceq1.mm"
include "fvmptg.mm"
include "sylan2.mm"
include "expcom.mm"
include "wn.mm"
include "c0.mm"
include "wa.mm"
include "cdm.mm"
include "cmpt.mm"
include "dmeqi.mm"
include "wral.mm"
include "ralrimivw.mm"
include "dmmptg.mm"
include "syl.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "notbid.mm"
include "ndmfv.mm"
include "syl6bir.mm"
include "wne.mm"
include "ecdmn0.mm"
include "wer.mm"
include "erdm.mm"
include "biimpd.mm"
include "syl5bir.mm"
include "necon1bd.mm"
include "jcad.mm"
include "eqtr3.mm"
include "syl6.mm"
include "pm2.61d.mm"

theorem divsfval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let c.sm: class .~
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  assume ercpbl.r: |- ( ph -> .~ Er V )
  assume ercpbl.v: |- ( ph -> V e. _V )
  assume ercpbl.f: |- F = ( x e. V |-> [ x ] .~ )

  disjoint .~ x
  disjoint A x
  disjoint V x
  disjoint ph x
  disjoint a b
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint B b
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint V a
  disjoint V b
  disjoint .+ a
  disjoint .+ b
  disjoint .+ x
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( F ` A ) = [ A ] .~ )

  proof
    wph
    cA
    cV
    wcel
    #
    cA
    cF
    cfv
    #
    cA
    c.sm
    cec
    #
    wceq
    #
    @0
    wph
    @3
    wph
    @0
    @2
    cvv
    wcel
    @3
    wph
    @2
    cV
    cvv
    ercpbl.v
    wph
    cA
    c.sm
    cV
    ercpbl.r
    ecss
    ssexd
    vx
    cA
    vx
    cv
    #
    c.sm
    cec
    #
    @2
    cV
    cvv
    cF
    @4
    cA
    c.sm
    eceq1
    ercpbl.f
    fvmptg
    sylan2
    expcom
    wph
    @0
    wn
    #
    @1
    c0
    wceq
    #
    @2
    c0
    wceq
    #
    wa
    @3
    wph
    @6
    @7
    @8
    wph
    @6
    cA
    cF
    cdm
    #
    wcel
    #
    wn
    @7
    wph
    @10
    @0
    wph
    @9
    cV
    cA
    wph
    @9
    vx
    cV
    @5
    cmpt
    #
    cdm
    #
    cV
    cF
    @11
    ercpbl.f
    dmeqi
    wph
    @5
    cvv
    wcel
    #
    vx
    cV
    wral
    @12
    cV
    wceq
    wph
    @13
    vx
    cV
    wph
    @5
    cV
    cvv
    ercpbl.v
    wph
    @4
    c.sm
    cV
    ercpbl.r
    ecss
    ssexd
    ralrimivw
    vx
    cV
    @5
    cvv
    dmmptg
    syl
    syl5eq
    eleq2d
    notbid
    cA
    cF
    ndmfv
    syl6bir
    wph
    @0
    @2
    c0
    @2
    c0
    wne
    cA
    c.sm
    cdm
    #
    wcel
    #
    wph
    @0
    cA
    c.sm
    ecdmn0
    wph
    @15
    @0
    wph
    @14
    cV
    cA
    wph
    cV
    c.sm
    wer
    @14
    cV
    wceq
    ercpbl.r
    cV
    c.sm
    erdm
    syl
    eleq2d
    biimpd
    syl5bir
    necon1bd
    jcad
    @1
    @2
    c0
    eqtr3
    syl6
    pm2.61d
end
