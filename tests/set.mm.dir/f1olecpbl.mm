include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "f1ocpbllem.mm"
include "breq12.mm"
include "syl6bi.mm"

theorem f1olecpbl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cN: class N
  let cV: class V
  let cX: class X
  assume f1ocpbl.f: |- ( ph -> F : V -1-1-onto-> X )


  assert |- ( ( ph /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) -> ( ( ( F ` A ) = ( F ` C ) /\ ( F ` B ) = ( F ` D ) ) -> ( A N B <-> C N D ) ) )

  proof
    wph
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    cC
    cV
    wcel
    cD
    cV
    wcel
    wa
    w3a
    cA
    cF
    cfv
    cC
    cF
    cfv
    wceq
    cB
    cF
    cfv
    cD
    cF
    cfv
    wceq
    wa
    cA
    cC
    wceq
    cB
    cD
    wceq
    wa
    cA
    cB
    cN
    wbr
    cC
    cD
    cN
    wbr
    wb
    wph
    cA
    cB
    cC
    cD
    cF
    cV
    cX
    f1ocpbl.f
    f1ocpbllem
    cA
    cC
    cB
    cD
    cN
    breq12
    syl6bi
end
