include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cun.mm"
include "ccom.mm"
include "ssun1.mm"
include "coires1.mm"
include "wrel.mm"
include "cdm.mm"
include "wss.mm"
include "wceq.mm"
include "ustrel.mm"
include "cxp.mm"
include "ustssxp.mm"
include "dmss.mm"
include "syl.mm"
include "dmxpid.mm"
include "syl6sseq.mm"
include "relssres.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "uneq1d.mm"
include "syl5sseqr.mm"
include "coundi.mm"
include "syl6sseqr.mm"
include "ustdiag.mm"
include "ssequn1.mm"
include "sylib.mm"
include "coeq2d.mm"
include "sseqtrd.mm"

theorem ustssco
  let cU: class U
  let cV: class V
  let cX: class X


  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U ) -> V C_ ( V o. V ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    cV
    cU
    wcel
    wa
    #
    cV
    cV
    cid
    cX
    cres
    #
    cV
    cun
    #
    ccom
    #
    cV
    cV
    ccom
    #
    @0
    cV
    cV
    @1
    ccom
    #
    @4
    cun
    #
    @3
    @0
    cV
    @4
    cun
    cV
    @6
    cV
    @4
    ssun1
    @0
    @5
    cV
    @4
    @0
    @5
    cV
    cX
    cres
    #
    cV
    cV
    cX
    coires1
    @0
    cV
    wrel
    cV
    cdm
    #
    cX
    wss
    @7
    cV
    wceq
    cU
    cV
    cX
    ustrel
    @0
    @8
    cX
    cX
    cxp
    #
    cdm
    #
    cX
    @0
    cV
    @9
    wss
    @8
    @10
    wss
    cU
    cV
    cX
    ustssxp
    cV
    @9
    dmss
    syl
    cX
    dmxpid
    syl6sseq
    cV
    cX
    relssres
    syl2anc
    syl5eq
    uneq1d
    syl5sseqr
    cV
    @1
    cV
    coundi
    syl6sseqr
    @0
    @2
    cV
    cV
    @0
    @1
    cV
    wss
    @2
    cV
    wceq
    cU
    cV
    cX
    ustdiag
    @1
    cV
    ssequn1
    sylib
    coeq2d
    sseqtrd
end
