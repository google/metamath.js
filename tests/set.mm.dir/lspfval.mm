include "wcel.mm"
include "clspn.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cbs.mm"
include "clss.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "rabeq.mm"
include "syl.mm"
include "inteqd.mm"
include "mpteq12dv.mm"
include "df-lsp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"

theorem lspfval
  let vt: setvar t
  let cS: class S
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vp: setvar p
  let vw: setvar w
  let cU: class U
  assume lspval.v: |- V = ( Base ` W )
  assume lspval.s: |- S = ( LSubSp ` W )
  assume lspval.n: |- N = ( LSpan ` W )

  disjoint s t
  disjoint S s
  disjoint S t
  disjoint V s
  disjoint V t
  disjoint W s
  disjoint p s
  disjoint p t
  disjoint p w
  disjoint S p
  disjoint s w
  disjoint t w
  disjoint S w
  disjoint U s
  disjoint U t
  disjoint V p
  disjoint V w
  disjoint W w
  assert |- ( W e. X -> N = ( s e. ~P V |-> |^| { t e. S | s C_ t } ) )

  proof
    cW
    cX
    wcel
    #
    cN
    cW
    clspn
    cfv
    #
    vs
    cV
    cpw
    #
    vs
    cv
    vt
    cv
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
    lspval.n
    @0
    cW
    cvv
    wcel
    @1
    @6
    wceq
    cW
    cX
    elex
    vw
    cW
    vs
    vw
    cv
    #
    cbs
    cfv
    #
    cpw
    #
    @3
    vt
    @7
    clss
    cfv
    #
    crab
    #
    cint
    #
    cmpt
    @6
    cvv
    clspn
    @7
    cW
    wceq
    #
    vs
    @9
    @12
    @2
    @5
    @13
    @8
    cV
    @13
    @8
    cW
    cbs
    cfv
    #
    cV
    @7
    cW
    cbs
    fveq2
    lspval.v
    syl6eqr
    pweqd
    @13
    @11
    @4
    @13
    @10
    cS
    wceq
    @11
    @4
    wceq
    @13
    @10
    cW
    clss
    cfv
    cS
    @7
    cW
    clss
    fveq2
    lspval.s
    syl6eqr
    @3
    vt
    @10
    cS
    rabeq
    syl
    inteqd
    mpteq12dv
    vw
    vt
    vs
    df-lsp
    vs
    @2
    @5
    cV
    cV
    @14
    cvv
    lspval.v
    cW
    cbs
    fvex
    eqeltri
    pwex
    mptex
    fvmpt
    syl
    syl5eq
end
