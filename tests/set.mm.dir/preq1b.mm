include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "wo.mm"
include "wcel.mm"
include "prid1g.mm"
include "syl.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "wb.mm"
include "elprg.mm"
include "sylibd.mm"
include "imp.mm"
include "syl5ibrcom.mm"
include "eqcom.mm"
include "eqeq2.mm"
include "oplem1.mm"
include "ex.mm"
include "preq1.mm"
include "impbid1.mm"

theorem preq1b
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  assume preq1b.a: |- ( ph -> A e. V )
  assume preq1b.b: |- ( ph -> B e. W )


  assert |- ( ph -> ( { A , C } = { B , C } <-> A = B ) )

  proof
    wph
    cA
    cC
    cpr
    #
    cB
    cC
    cpr
    #
    wceq
    #
    cA
    cB
    wceq
    #
    wph
    @2
    @3
    wph
    @2
    wa
    @3
    cA
    cC
    wceq
    #
    cB
    cA
    wceq
    #
    cB
    cC
    wceq
    #
    wph
    @2
    @3
    @4
    wo
    #
    wph
    @2
    cA
    @1
    wcel
    #
    @7
    wph
    cA
    @0
    wcel
    #
    @2
    @8
    wph
    cA
    cV
    wcel
    #
    @9
    preq1b.a
    cA
    cC
    cV
    prid1g
    syl
    @0
    @1
    cA
    eleq2
    syl5ibcom
    wph
    @10
    @8
    @7
    wb
    preq1b.a
    cA
    cB
    cC
    cV
    elprg
    syl
    sylibd
    imp
    wph
    @2
    @5
    @6
    wo
    #
    wph
    @2
    cB
    @0
    wcel
    #
    @11
    wph
    @12
    @2
    cB
    @1
    wcel
    #
    wph
    cB
    cW
    wcel
    #
    @13
    preq1b.b
    cB
    cC
    cW
    prid1g
    syl
    @0
    @1
    cB
    eleq2
    syl5ibrcom
    wph
    @14
    @12
    @11
    wb
    preq1b.b
    cB
    cA
    cC
    cW
    elprg
    syl
    sylibd
    imp
    cA
    cB
    eqcom
    cA
    cC
    cB
    eqeq2
    oplem1
    ex
    cA
    cB
    cC
    preq1
    impbid1
end
