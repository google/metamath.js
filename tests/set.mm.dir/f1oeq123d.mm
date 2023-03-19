include "wf1o.mm"
include "wceq.mm"
include "wb.mm"
include "f1oeq1.mm"
include "syl.mm"
include "f1oeq2.mm"
include "f1oeq3.mm"
include "3bitrd.mm"

theorem f1oeq123d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume f1eq123d.1: |- ( ph -> F = G )
  assume f1eq123d.2: |- ( ph -> A = B )
  assume f1eq123d.3: |- ( ph -> C = D )


  assert |- ( ph -> ( F : A -1-1-onto-> C <-> G : B -1-1-onto-> D ) )

  proof
    wph
    cA
    cC
    cF
    wf1o
    #
    cA
    cC
    cG
    wf1o
    #
    cB
    cC
    cG
    wf1o
    #
    cB
    cD
    cG
    wf1o
    #
    wph
    cF
    cG
    wceq
    @0
    @1
    wb
    f1eq123d.1
    cA
    cC
    cF
    cG
    f1oeq1
    syl
    wph
    cA
    cB
    wceq
    @1
    @2
    wb
    f1eq123d.2
    cA
    cB
    cC
    cG
    f1oeq2
    syl
    wph
    cC
    cD
    wceq
    @2
    @3
    wb
    f1eq123d.3
    cC
    cD
    cB
    cG
    f1oeq3
    syl
    3bitrd
end
