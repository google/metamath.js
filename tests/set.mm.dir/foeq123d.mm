include "wfo.mm"
include "wceq.mm"
include "wb.mm"
include "foeq1.mm"
include "syl.mm"
include "foeq2.mm"
include "foeq3.mm"
include "3bitrd.mm"

theorem foeq123d
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


  assert |- ( ph -> ( F : A -onto-> C <-> G : B -onto-> D ) )

  proof
    wph
    cA
    cC
    cF
    wfo
    #
    cA
    cC
    cG
    wfo
    #
    cB
    cC
    cG
    wfo
    #
    cB
    cD
    cG
    wfo
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
    foeq1
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
    foeq2
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
    foeq3
    syl
    3bitrd
end
