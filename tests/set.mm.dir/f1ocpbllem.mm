include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wf1.mm"
include "wb.mm"
include "wf1o.mm"
include "f1of1.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp3l.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "simp2r.mm"
include "simp3r.mm"
include "anbi12d.mm"

theorem f1ocpbllem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  let cX: class X
  assume f1ocpbl.f: |- ( ph -> F : V -1-1-onto-> X )


  assert |- ( ( ph /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) -> ( ( ( F ` A ) = ( F ` C ) /\ ( F ` B ) = ( F ` D ) ) <-> ( A = C /\ B = D ) ) )

  proof
    wph
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cC
    cV
    wcel
    #
    cD
    cV
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cF
    cfv
    cC
    cF
    cfv
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cF
    cfv
    cD
    cF
    cfv
    wceq
    #
    cB
    cD
    wceq
    #
    @6
    cV
    cX
    cF
    wf1
    #
    @0
    @3
    @7
    @8
    wb
    wph
    @2
    @11
    @5
    wph
    cV
    cX
    cF
    wf1o
    @11
    f1ocpbl.f
    cV
    cX
    cF
    f1of1
    syl
    3ad2ant1
    #
    wph
    @0
    @1
    @5
    simp2l
    wph
    @2
    @3
    @4
    simp3l
    cV
    cX
    cA
    cC
    cF
    f1fveq
    syl12anc
    @6
    @11
    @1
    @4
    @9
    @10
    wb
    @12
    wph
    @0
    @1
    @5
    simp2r
    wph
    @2
    @3
    @4
    simp3r
    cV
    cX
    cB
    cD
    cF
    f1fveq
    syl12anc
    anbi12d
end
