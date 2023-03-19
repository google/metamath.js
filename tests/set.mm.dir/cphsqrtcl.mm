include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "ccph.mm"
include "csqrt.mm"
include "cfv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "cima.mm"
include "simp1.mm"
include "wa.mm"
include "elrege0.mm"
include "biimpri.mm"
include "3adant1.mm"
include "elind.mm"
include "cc.mm"
include "wfn.mm"
include "wss.mm"
include "wf.mm"
include "sqrtf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "inss2.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "fnfvima.mm"
include "mp3an12.mm"
include "syl.mm"
include "cphl.mm"
include "cnlm.mm"
include "ccnfld.mm"
include "cress.mm"
include "wceq.mm"
include "cnm.mm"
include "cbs.mm"
include "cv.mm"
include "cip.mm"
include "cmpt.mm"
include "eqid.mm"
include "iscph.mm"
include "simp2bi.mm"
include "sselda.mm"
include "sylan2.mm"

theorem cphsqrtcl
  let cA: class A
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume cphsca.f: |- F = ( Scalar ` W )
  assume cphsca.k: |- K = ( Base ` F )


  assert |- ( ( W e. CPreHil /\ ( A e. K /\ A e. RR /\ 0 <_ A ) ) -> ( sqrt ` A ) e. K )

  proof
    cA
    cK
    wcel
    #
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    w3a
    #
    cW
    ccph
    wcel
    #
    cA
    csqrt
    cfv
    #
    csqrt
    cK
    cc0
    cpnf
    cico
    co
    #
    cin
    #
    cima
    #
    wcel
    #
    @5
    cK
    wcel
    @3
    cA
    @7
    wcel
    #
    @9
    @3
    cK
    @6
    cA
    @0
    @1
    @2
    simp1
    @1
    @2
    cA
    @6
    wcel
    #
    @0
    @11
    @1
    @2
    wa
    cA
    elrege0
    biimpri
    3adant1
    elind
    csqrt
    cc
    wfn
    #
    @7
    cc
    wss
    @10
    @9
    cc
    cc
    csqrt
    wf
    @12
    sqrtf
    cc
    cc
    csqrt
    ffn
    ax-mp
    @7
    @6
    cc
    cK
    @6
    inss2
    @6
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    sstri
    cc
    @7
    csqrt
    cA
    fnfvima
    mp3an12
    syl
    @4
    @8
    cK
    @5
    @4
    cW
    cphl
    wcel
    cW
    cnlm
    wcel
    cF
    ccnfld
    cK
    cress
    co
    wceq
    w3a
    @8
    cK
    wss
    cW
    cnm
    cfv
    #
    vx
    cW
    cbs
    cfv
    #
    vx
    cv
    #
    @15
    cW
    cip
    cfv
    #
    co
    csqrt
    cfv
    cmpt
    wceq
    vx
    cF
    @16
    cK
    @13
    @14
    cW
    @14
    eqid
    @16
    eqid
    @13
    eqid
    cphsca.f
    cphsca.k
    iscph
    simp2bi
    sselda
    sylan2
end
