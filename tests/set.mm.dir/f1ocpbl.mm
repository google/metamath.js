include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "f1ocpbllem.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "syl6bi.mm"

theorem f1ocpbl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cF: class F
  let cV: class V
  let cX: class X
  assume f1ocpbl.f: |- ( ph -> F : V -1-1-onto-> X )


  assert |- ( ( ph /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) -> ( ( ( F ` A ) = ( F ` C ) /\ ( F ` B ) = ( F ` D ) ) -> ( F ` ( A .+ B ) ) = ( F ` ( C .+ D ) ) ) )

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
    #
    cA
    cB
    c.pl
    co
    #
    cF
    cfv
    cC
    cD
    c.pl
    co
    #
    cF
    cfv
    wceq
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
    @0
    @1
    @2
    cF
    cA
    cC
    cB
    cD
    c.pl
    oveq12
    fveq2d
    syl6bi
end
