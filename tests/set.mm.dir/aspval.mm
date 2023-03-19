include "casa.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "csubrg.mm"
include "cin.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "wceq.mm"
include "casp.mm"
include "cbs.mm"
include "clss.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "ineq12d.mm"
include "rabeq.mm"
include "syl.mm"
include "inteqd.mm"
include "mpteq12dv.mm"
include "df-asp.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "adantr.mm"
include "simpr.mm"
include "elpw2.mm"
include "sylibr.mm"
include "wrex.mm"
include "crg.mm"
include "assaring.mm"
include "subrgid.mm"
include "clmod.mm"
include "assalmod.mm"
include "lss1.mm"
include "elind.mm"
include "sseq2.mm"
include "rspcev.mm"
include "sylan.mm"
include "intexrab.mm"
include "sylib.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem aspval
  let vt: setvar t
  let cA: class A
  let cS: class S
  let cL: class L
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vw: setvar w
  let cT: class T
  assume aspval.a: |- A = ( AlgSpan ` W )
  assume aspval.v: |- V = ( Base ` W )
  assume aspval.l: |- L = ( LSubSp ` W )

  disjoint L t
  disjoint S t
  disjoint V t
  disjoint W t
  disjoint s t
  disjoint s w
  disjoint L s
  disjoint t w
  disjoint L w
  disjoint S s
  disjoint T t
  disjoint V s
  disjoint V w
  disjoint W s
  disjoint W w
  assert |- ( ( W e. AssAlg /\ S C_ V ) -> ( A ` S ) = |^| { t e. ( ( SubRing ` W ) i^i L ) | S C_ t } )

  proof
    cW
    casa
    wcel
    #
    cS
    cV
    wss
    #
    wa
    #
    cS
    cA
    cfv
    #
    cS
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
    cW
    csubrg
    cfv
    #
    cL
    cin
    #
    crab
    #
    cint
    #
    cmpt
    #
    cfv
    #
    cS
    @6
    wss
    #
    vt
    @9
    crab
    #
    cint
    #
    @0
    @3
    @13
    wceq
    @1
    @0
    cS
    cA
    @12
    @0
    cA
    cW
    casp
    cfv
    @12
    aspval.a
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
    @7
    vt
    @17
    csubrg
    cfv
    #
    @17
    clss
    cfv
    #
    cin
    #
    crab
    #
    cint
    #
    cmpt
    @12
    casa
    casp
    @17
    cW
    wceq
    #
    vs
    @19
    @24
    @4
    @11
    @25
    @18
    cV
    @25
    @18
    cW
    cbs
    cfv
    #
    cV
    @17
    cW
    cbs
    fveq2
    aspval.v
    syl6eqr
    pweqd
    @25
    @23
    @10
    @25
    @22
    @9
    wceq
    @23
    @10
    wceq
    @25
    @20
    @8
    @21
    cL
    @17
    cW
    csubrg
    fveq2
    @25
    @21
    cW
    clss
    cfv
    cL
    @17
    cW
    clss
    fveq2
    aspval.l
    syl6eqr
    ineq12d
    @7
    vt
    @22
    @9
    rabeq
    syl
    inteqd
    mpteq12dv
    vw
    vt
    vs
    df-asp
    vs
    @4
    @11
    cV
    cV
    @26
    cvv
    aspval.v
    cW
    cbs
    fvex
    eqeltri
    #
    pwex
    mptex
    fvmpt
    syl5eq
    fveq1d
    adantr
    @2
    cS
    @4
    wcel
    #
    @16
    cvv
    wcel
    #
    @13
    @16
    wceq
    @2
    @1
    @28
    @0
    @1
    simpr
    cS
    cV
    @27
    elpw2
    sylibr
    @2
    @14
    vt
    @9
    wrex
    #
    @29
    @0
    cV
    @9
    wcel
    @1
    @30
    @0
    @8
    cL
    cV
    @0
    cW
    crg
    wcel
    cV
    @8
    wcel
    cW
    assaring
    cV
    cW
    aspval.v
    subrgid
    syl
    @0
    cW
    clmod
    wcel
    cV
    cL
    wcel
    cW
    assalmod
    cL
    cV
    cW
    aspval.v
    aspval.l
    lss1
    syl
    elind
    @14
    @1
    vt
    cV
    @9
    @6
    cV
    cS
    sseq2
    rspcev
    sylan
    @14
    vt
    @9
    intexrab
    sylib
    vs
    cS
    @11
    @16
    @4
    cvv
    @12
    @5
    cS
    wceq
    #
    @10
    @15
    @31
    @7
    @14
    vt
    @9
    @5
    cS
    @6
    sseq1
    rabbidv
    inteqd
    @12
    eqid
    fvmptg
    syl2anc
    eqtrd
end
