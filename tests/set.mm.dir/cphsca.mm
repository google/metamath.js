include "ccph.mm"
include "wcel.mm"
include "cphl.mm"
include "cnlm.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "csqrt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cin.mm"
include "cima.mm"
include "wss.mm"
include "cnm.mm"
include "cfv.mm"
include "cbs.mm"
include "cv.mm"
include "cip.mm"
include "cmpt.mm"
include "eqid.mm"
include "iscph.mm"
include "simp1bi.mm"
include "simp3d.mm"

theorem cphsca
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume cphsca.f: |- F = ( Scalar ` W )
  assume cphsca.k: |- K = ( Base ` F )


  assert |- ( W e. CPreHil -> F = ( CCfld |`s K ) )

  proof
    cW
    ccph
    wcel
    #
    cW
    cphl
    wcel
    #
    cW
    cnlm
    wcel
    #
    cF
    ccnfld
    cK
    cress
    co
    wceq
    #
    @0
    @1
    @2
    @3
    w3a
    csqrt
    cK
    cc0
    cpnf
    cico
    co
    cin
    cima
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
    @6
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
    @7
    cK
    @4
    @5
    cW
    @5
    eqid
    @7
    eqid
    @4
    eqid
    cphsca.f
    cphsca.k
    iscph
    simp1bi
    simp3d
end
