include "wcel.mm"
include "ccmp.mm"
include "wf.mm"
include "cufl.mm"
include "ccrd.mm"
include "cdm.mm"
include "cin.mm"
include "w3a.mm"
include "cpt.mm"
include "cfv.mm"
include "cv.mm"
include "cuni.mm"
include "cixp.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "cmpt2.mm"
include "nfcv.mm"
include "fveq2.mm"
include "weq.mm"
include "mpteq2dv.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "imaeq2.mm"
include "sylan9eq.mm"
include "cbvmpt2x.mm"
include "unieqd.mm"
include "cbvixpv.mm"
include "simp1.mm"
include "simp2.mm"
include "ctop.mm"
include "wceq.mm"
include "wss.mm"
include "cmptop.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "ptuni.mm"
include "syl2anc.mm"
include "syl6eqr.mm"
include "simp3.mm"
include "eqeltrd.mm"
include "ptcmplem5.mm"
include "syl5eqel.mm"

theorem ptcmpg
  let cA: class A
  let cF: class F
  let cJ: class J
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  assume ptcmpg.1: |- J = ( Xt_ ` F )
  assume ptcmpg.2: |- X = U. J


  assert |- ( ( A e. V /\ F : A --> Comp /\ X e. ( UFL i^i dom card ) ) -> J e. Comp )

  proof
    cA
    cV
    wcel
    #
    cA
    ccmp
    cF
    wf
    #
    cX
    cufl
    ccrd
    cdm
    cin
    #
    wcel
    #
    w3a
    #
    cJ
    cF
    cpt
    cfv
    ccmp
    ptcmpg.1
    @4
    vw
    vu
    cA
    va
    vb
    cA
    va
    cv
    #
    cF
    cfv
    #
    vw
    vn
    cA
    vn
    cv
    #
    cF
    cfv
    #
    cuni
    #
    cixp
    #
    @5
    vw
    cv
    #
    cfv
    #
    cmpt
    #
    ccnv
    #
    vb
    cv
    #
    cima
    #
    cmpt2
    vk
    vm
    cF
    cV
    @10
    va
    vb
    vk
    vu
    cA
    @6
    @16
    vk
    cv
    #
    cF
    cfv
    #
    vw
    @10
    @17
    @11
    cfv
    #
    cmpt
    #
    ccnv
    #
    vu
    cv
    #
    cima
    #
    vk
    @6
    nfcv
    va
    @18
    nfcv
    vk
    @16
    nfcv
    vu
    @16
    nfcv
    va
    @23
    nfcv
    vb
    @23
    nfcv
    @5
    @17
    cF
    fveq2
    va
    vk
    weq
    #
    vb
    vu
    weq
    @16
    @21
    @15
    cima
    @23
    @24
    @14
    @21
    @15
    @24
    @13
    @20
    @24
    vw
    @10
    @12
    @19
    @5
    @17
    @11
    fveq2
    mpteq2dv
    cnveqd
    imaeq1d
    @15
    @22
    @21
    imaeq2
    sylan9eq
    cbvmpt2x
    vn
    vm
    cA
    @9
    vm
    cv
    #
    cF
    cfv
    #
    cuni
    vn
    vm
    weq
    @8
    @26
    @7
    @25
    cF
    fveq2
    unieqd
    cbvixpv
    @0
    @1
    @3
    simp1
    #
    @0
    @1
    @3
    simp2
    #
    @4
    @10
    cX
    @2
    @4
    @10
    cJ
    cuni
    #
    cX
    @4
    @0
    cA
    ctop
    cF
    wf
    #
    @10
    @29
    wceq
    @27
    @4
    @1
    ccmp
    ctop
    wss
    @30
    @28
    vk
    ccmp
    ctop
    @17
    cmptop
    ssriv
    cA
    ccmp
    ctop
    cF
    fss
    sylancl
    vn
    cA
    cF
    cJ
    cV
    ptcmpg.1
    ptuni
    syl2anc
    ptcmpg.2
    syl6eqr
    @0
    @1
    @3
    simp3
    eqeltrd
    ptcmplem5
    syl5eqel
end
