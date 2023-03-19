include "cmpt.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "eqid.mm"
include "fmptd.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "cncfrss2.mm"
include "syl.mm"
include "sstrd.mm"
include "cv.mm"
include "cfv.mm"
include "wa.mm"
include "wceq.mm"
include "sselda.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "cncfmptss.mm"
include "eqeltrrd.mm"
include "cncffvrn.mm"
include "mpbird.mm"

theorem cncfmptssg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let vk: setvar k
  assume cncfmptssg.2: |- F = ( x e. A |-> E )
  assume cncfmptssg.3: |- ( ph -> F e. ( A -cn-> B ) )
  assume cncfmptssg.4: |- ( ph -> C C_ A )
  assume cncfmptssg.5: |- ( ph -> D C_ B )
  assume cncfmptssg.6: |- ( ( ph /\ x e. C ) -> E e. D )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( x e. C |-> E ) e. ( C -cn-> D ) )

  proof
    wph
    vx
    cC
    cE
    cmpt
    #
    cC
    cD
    ccncf
    co
    wcel
    #
    cC
    cD
    @0
    wf
    #
    wph
    vx
    cC
    cE
    cD
    @0
    cncfmptssg.6
    @0
    eqid
    fmptd
    wph
    cD
    cc
    wss
    @0
    cC
    cB
    ccncf
    co
    #
    wcel
    @1
    @2
    wb
    wph
    cD
    cB
    cc
    cncfmptssg.5
    wph
    cF
    cA
    cB
    ccncf
    co
    wcel
    cB
    cc
    wss
    cncfmptssg.3
    cA
    cB
    cF
    cncfrss2
    syl
    sstrd
    wph
    vx
    cC
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    @0
    @3
    wph
    vx
    cC
    @5
    cE
    wph
    @4
    cC
    wcel
    wa
    @4
    cA
    wcel
    cE
    cD
    wcel
    @5
    cE
    wceq
    wph
    cC
    cA
    @4
    cncfmptssg.4
    sselda
    cncfmptssg.6
    vx
    cA
    cE
    cD
    cF
    cncfmptssg.2
    fvmpt2
    syl2anc
    mpteq2dva
    wph
    vx
    cA
    cB
    cC
    cF
    vx
    cF
    vx
    cA
    cE
    cmpt
    cncfmptssg.2
    vx
    cA
    cE
    nfmpt1
    nfcxfr
    cncfmptssg.3
    cncfmptssg.4
    cncfmptss
    eqeltrrd
    cC
    cB
    cD
    @0
    cncffvrn
    syl2anc
    mpbird
end
