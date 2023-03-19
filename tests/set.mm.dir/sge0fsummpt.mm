include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cv.mm"
include "csu.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0fsum.mm"
include "wceq.mm"
include "fveq2.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nffv.mm"
include "cbvsum.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "sumeq2dv.mm"
include "3eqtrd.mm"

theorem sge0fsummpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vj: setvar j
  let vx: setvar x
  assume sge0fsummpt.a: |- ( ph -> A e. Fin )
  assume sge0fsummpt.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) )

  disjoint A k
  disjoint k ph
  disjoint A j
  disjoint j k
  disjoint B j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. A |-> B ) ) = sum_ k e. A B )

  proof
    wph
    vk
    cA
    cB
    cmpt
    #
    csumge0
    cfv
    cA
    vj
    cv
    #
    @0
    cfv
    #
    vj
    csu
    #
    cA
    vk
    cv
    #
    @0
    cfv
    #
    vk
    csu
    #
    cA
    cB
    vk
    csu
    wph
    vj
    @0
    cA
    sge0fsummpt.a
    wph
    vk
    cA
    cB
    cc0
    cpnf
    cico
    co
    #
    @0
    sge0fsummpt.b
    @0
    eqid
    #
    fmptd
    sge0fsum
    @3
    @6
    wceq
    wph
    cA
    @2
    @5
    vj
    vk
    @1
    @4
    @0
    fveq2
    vk
    cA
    nfcv
    vj
    cA
    nfcv
    vk
    @1
    @0
    vk
    cA
    cB
    nfmpt1
    vk
    @1
    nfcv
    nffv
    vj
    @5
    nfcv
    cbvsum
    a1i
    wph
    cA
    @5
    cB
    vk
    wph
    @4
    cA
    wcel
    #
    wa
    @9
    cB
    @7
    wcel
    @5
    cB
    wceq
    wph
    @9
    simpr
    sge0fsummpt.b
    vk
    cA
    cB
    @7
    @0
    @8
    fvmpt2
    syl2anc
    sumeq2dv
    3eqtrd
end
