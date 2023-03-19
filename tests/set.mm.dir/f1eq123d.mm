include "wf1.mm"
include "wceq.mm"
include "wb.mm"
include "f1eq1.mm"
include "syl.mm"
include "f1eq2.mm"
include "f1eq3.mm"
include "3bitrd.mm"

theorem f1eq123d
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


  assert |- ( ph -> ( F : A -1-1-> C <-> G : B -1-1-> D ) )

  proof
    wph
    cA
    cC
    cF
    wf1
    #
    cA
    cC
    cG
    wf1
    #
    cB
    cC
    cG
    wf1
    #
    cB
    cD
    cG
    wf1
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
    f1eq1
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
    f1eq2
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
    f1eq3
    syl
    3bitrd
end
