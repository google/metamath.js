include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wf1o.mm"
include "cv.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "crab.mm"
include "weq.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "elrab2.mm"
include "csymg.mm"
include "eqid.mm"
include "elsymgbas2.mm"
include "anbi1d.mm"
include "syl5bb.mm"

theorem symgfixelq
  let cP: class P
  let cQ: class Q
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let vq: setvar q
  let vf: setvar f
  assume symgfixf.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume symgfixf.q: |- Q = { q e. P | ( q ` K ) = K }

  disjoint K q
  disjoint P q
  disjoint f q
  disjoint F f
  disjoint K f
  disjoint P f
  assert |- ( F e. V -> ( F e. Q <-> ( F : N -1-1-onto-> N /\ ( F ` K ) = K ) ) )

  proof
    cF
    cQ
    wcel
    cF
    cP
    wcel
    #
    cK
    cF
    cfv
    #
    cK
    wceq
    #
    wa
    cF
    cV
    wcel
    #
    cN
    cN
    cF
    wf1o
    #
    @2
    wa
    cK
    vf
    cv
    #
    cfv
    #
    cK
    wceq
    #
    @2
    vf
    cF
    cP
    cQ
    @5
    cF
    wceq
    @6
    @1
    cK
    cK
    @5
    cF
    fveq1
    eqeq1d
    cQ
    cK
    vq
    cv
    #
    cfv
    #
    cK
    wceq
    #
    vq
    cP
    crab
    @7
    vf
    cP
    crab
    symgfixf.q
    @10
    @7
    vq
    vf
    cP
    vq
    vf
    weq
    @9
    @6
    cK
    cK
    @8
    @5
    fveq1
    eqeq1d
    cbvrabv
    eqtri
    elrab2
    @3
    @0
    @4
    @2
    cN
    cP
    cF
    cN
    csymg
    cfv
    #
    cV
    @11
    eqid
    symgfixf.p
    elsymgbas2
    anbi1d
    syl5bb
end
