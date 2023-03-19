include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccom.mm"
include "wss.mm"
include "ccnv.mm"
include "wceq.mm"
include "wrex.mm"
include "cin.mm"
include "simplll.mm"
include "simplr.mm"
include "ustinvel.mm"
include "syl2anc.mm"
include "ustincl.mm"
include "syl3anc.mm"
include "wrel.mm"
include "ustrel.mm"
include "dfrel2.mm"
include "sylib.mm"
include "ineq1d.mm"
include "cnvin.mm"
include "incom.mm"
include "3eqtr4g.mm"
include "inss2.mm"
include "ustssco.mm"
include "simpr.mm"
include "sstrd.mm"
include "syl5ss.mm"
include "cnveq.mm"
include "id.mm"
include "eqeq12d.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ustexhalf.mm"
include "r19.29a.mm"

theorem ustexsym
  let vw: setvar w
  let cU: class U
  let cV: class V
  let cX: class X
  let vx: setvar x

  disjoint U w
  disjoint V w
  disjoint w x
  disjoint U x
  disjoint V x
  disjoint X x
  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U ) -> E. w e. U ( `' w = w /\ w C_ V ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cV
    cU
    wcel
    #
    wa
    #
    vx
    cv
    #
    @3
    ccom
    #
    cV
    wss
    #
    vw
    cv
    #
    ccnv
    #
    @6
    wceq
    #
    @6
    cV
    wss
    #
    wa
    #
    vw
    cU
    wrex
    #
    vx
    cU
    @2
    @3
    cU
    wcel
    #
    wa
    #
    @5
    wa
    #
    @3
    ccnv
    #
    @3
    cin
    #
    cU
    wcel
    #
    @16
    ccnv
    #
    @16
    wceq
    #
    @16
    cV
    wss
    #
    @11
    @14
    @0
    @15
    cU
    wcel
    #
    @12
    @17
    @0
    @1
    @12
    @5
    simplll
    #
    @14
    @0
    @12
    @21
    @22
    @2
    @12
    @5
    simplr
    #
    cU
    @3
    cX
    ustinvel
    syl2anc
    @23
    cU
    @15
    @3
    cX
    ustincl
    syl3anc
    @14
    @0
    @12
    @19
    @22
    @23
    @0
    @12
    wa
    #
    @15
    ccnv
    #
    @15
    cin
    @3
    @15
    cin
    @18
    @16
    @24
    @25
    @3
    @15
    @24
    @3
    wrel
    @25
    @3
    wceq
    cU
    @3
    cX
    ustrel
    @3
    dfrel2
    sylib
    ineq1d
    @15
    @3
    cnvin
    @15
    @3
    incom
    3eqtr4g
    syl2anc
    @14
    @16
    @3
    cV
    @15
    @3
    inss2
    @14
    @3
    @4
    cV
    @14
    @0
    @12
    @3
    @4
    wss
    @22
    @23
    cU
    @3
    cX
    ustssco
    syl2anc
    @13
    @5
    simpr
    sstrd
    syl5ss
    @10
    @19
    @20
    wa
    vw
    @16
    cU
    @6
    @16
    wceq
    #
    @8
    @19
    @9
    @20
    @26
    @7
    @18
    @6
    @16
    @6
    @16
    cnveq
    @26
    id
    eqeq12d
    @6
    @16
    cV
    sseq1
    anbi12d
    rspcev
    syl12anc
    vx
    cU
    cV
    cX
    ustexhalf
    r19.29a
end
