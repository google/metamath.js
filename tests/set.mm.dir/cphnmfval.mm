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
include "cv.mm"
include "cmpt.mm"
include "eqid.mm"
include "iscph.mm"
include "simp3bi.mm"

theorem cphnmfval
  let vx: setvar x
  let c.xi: class .,
  let cN: class N
  let cV: class V
  let cW: class W
  let cA: class A
  let cK: class K
  assume nmsq.v: |- V = ( Base ` W )
  assume nmsq.h: |- ., = ( .i ` W )
  assume nmsq.n: |- N = ( norm ` W )

  disjoint ., x
  disjoint V x
  disjoint W x
  disjoint A x
  disjoint K x
  assert |- ( W e. CPreHil -> N = ( x e. V |-> ( sqrt ` ( x ., x ) ) ) )

  proof
    cW
    ccph
    wcel
    cW
    cphl
    wcel
    cW
    cnlm
    wcel
    cW
    csca
    cfv
    #
    ccnfld
    @0
    cbs
    cfv
    #
    cress
    co
    wceq
    w3a
    csqrt
    @1
    cc0
    cpnf
    cico
    co
    cin
    cima
    @1
    wss
    cN
    vx
    cV
    vx
    cv
    #
    @2
    c.xi
    co
    csqrt
    cfv
    cmpt
    wceq
    vx
    @0
    c.xi
    @1
    cN
    cV
    cW
    nmsq.v
    nmsq.h
    nmsq.n
    @0
    eqid
    @1
    eqid
    iscph
    simp3bi
end
