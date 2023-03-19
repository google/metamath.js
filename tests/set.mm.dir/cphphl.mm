include "ccph.mm"
include "wcel.mm"
include "cphl.mm"
include "cnlm.mm"
include "csca.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cbs.mm"
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
include "cv.mm"
include "cip.mm"
include "cmpt.mm"
include "eqid.mm"
include "iscph.mm"
include "simp1bi.mm"
include "simp1d.mm"

theorem cphphl
  let cW: class W
  let vx: setvar x


  assert |- ( W e. CPreHil -> W e. PreHil )

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
    cW
    csca
    cfv
    #
    ccnfld
    @3
    cbs
    cfv
    #
    cress
    co
    wceq
    #
    @0
    @1
    @2
    @5
    w3a
    csqrt
    @4
    cc0
    cpnf
    cico
    co
    cin
    cima
    @4
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
    @8
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
    @3
    @9
    @4
    @6
    @7
    cW
    @7
    eqid
    @9
    eqid
    @6
    eqid
    @3
    eqid
    @4
    eqid
    iscph
    simp1bi
    simp1d
end
