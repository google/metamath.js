include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "wceq.mm"
include "lspfval.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cvv.mm"
include "simpr.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "sylibr.mm"
include "wrex.mm"
include "lss1.mm"
include "sseq2.mm"
include "rspcev.mm"
include "sylan.mm"
include "intexrab.mm"
include "sylib.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem lspval
  let vt: setvar t
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vs: setvar s
  let vw: setvar w
  assume lspval.v: |- V = ( Base ` W )
  assume lspval.s: |- S = ( LSubSp ` W )
  assume lspval.n: |- N = ( LSpan ` W )

  disjoint S t
  disjoint U t
  disjoint V t
  disjoint p s
  disjoint p t
  disjoint p w
  disjoint S p
  disjoint s t
  disjoint s w
  disjoint S s
  disjoint t w
  disjoint S w
  disjoint U s
  disjoint V p
  disjoint V s
  disjoint V w
  disjoint W s
  disjoint W w
  assert |- ( ( W e. LMod /\ U C_ V ) -> ( N ` U ) = |^| { t e. S | U C_ t } )

  proof
    cW
    clmod
    wcel
    #
    cU
    cV
    wss
    #
    wa
    #
    cU
    cN
    cfv
    #
    cU
    vs
    cV
    cpw
    #
    vs
    cv
    #
    vt
    cv
    #
    wss
    #
    vt
    cS
    crab
    #
    cint
    #
    cmpt
    #
    cfv
    #
    cU
    @6
    wss
    #
    vt
    cS
    crab
    #
    cint
    #
    @0
    @3
    @11
    wceq
    @1
    @0
    cU
    cN
    @10
    vt
    cS
    cN
    cV
    cW
    clmod
    vs
    lspval.v
    lspval.s
    lspval.n
    lspfval
    fveq1d
    adantr
    @2
    cU
    @4
    wcel
    #
    @14
    cvv
    wcel
    #
    @11
    @14
    wceq
    @2
    @1
    @15
    @0
    @1
    simpr
    cU
    cV
    cV
    cW
    cbs
    cfv
    cvv
    lspval.v
    cW
    cbs
    fvex
    eqeltri
    elpw2
    sylibr
    @2
    @12
    vt
    cS
    wrex
    #
    @16
    @0
    cV
    cS
    wcel
    @1
    @17
    cS
    cV
    cW
    lspval.v
    lspval.s
    lss1
    @12
    @1
    vt
    cV
    cS
    @6
    cV
    cU
    sseq2
    rspcev
    sylan
    @12
    vt
    cS
    intexrab
    sylib
    vs
    cU
    @9
    @14
    @4
    cvv
    @10
    @5
    cU
    wceq
    #
    @8
    @13
    @18
    @7
    @12
    vt
    cS
    @5
    cU
    @6
    sseq1
    rabbidv
    inteqd
    @10
    eqid
    fvmptg
    syl2anc
    eqtrd
end
