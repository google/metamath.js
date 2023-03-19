include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "wf1.mm"
include "wb.mm"
include "wf1o.mm"
include "f1of1.mm"
include "syl.mm"
include "adantr.mm"
include "simpr2.mm"
include "simpr3.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "syl6bi.mm"

theorem f1ovscpbl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let cF: class F
  let cK: class K
  let cV: class V
  let cX: class X
  assume f1ocpbl.f: |- ( ph -> F : V -1-1-onto-> X )


  assert |- ( ( ph /\ ( A e. K /\ B e. V /\ C e. V ) ) -> ( ( F ` B ) = ( F ` C ) -> ( F ` ( A .+ B ) ) = ( F ` ( A .+ C ) ) ) )

  proof
    wph
    cA
    cK
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cB
    cF
    cfv
    cC
    cF
    cfv
    wceq
    #
    cB
    cC
    wceq
    #
    cA
    cB
    c.pl
    co
    #
    cF
    cfv
    cA
    cC
    c.pl
    co
    #
    cF
    cfv
    wceq
    @4
    cV
    cX
    cF
    wf1
    #
    @1
    @2
    @5
    @6
    wb
    wph
    @9
    @3
    wph
    cV
    cX
    cF
    wf1o
    @9
    f1ocpbl.f
    cV
    cX
    cF
    f1of1
    syl
    adantr
    wph
    @0
    @1
    @2
    simpr2
    wph
    @0
    @1
    @2
    simpr3
    cV
    cX
    cB
    cC
    cF
    f1fveq
    syl12anc
    @6
    @7
    @8
    cF
    cB
    cC
    cA
    c.pl
    oveq2
    fveq2d
    syl6bi
end
