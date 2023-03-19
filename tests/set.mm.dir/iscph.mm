include "cphl.mm"
include "cnlm.mm"
include "cin.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "csqrt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cima.mm"
include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "w3a.mm"
include "ccph.mm"
include "elin.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "cnm.mm"
include "cbs.mm"
include "cip.mm"
include "wsbc.mm"
include "csca.mm"
include "cvv.mm"
include "fvexd.mm"
include "simplr.mm"
include "simpll.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "ineq1d.mm"
include "imaeq2d.mm"
include "sseq12d.mm"
include "oveqd.mm"
include "mpteq12dv.mm"
include "3anbi123d.mm"
include "3anass.mm"
include "syl6bb.mm"
include "sbcied.mm"
include "df-cph.mm"
include "elrab2.mm"
include "anass.mm"
include "3bitr4i.mm"

theorem iscph
  let vx: setvar x
  let cF: class F
  let c.xi: class .,
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vk: setvar k
  let vw: setvar w
  assume iscph.v: |- V = ( Base ` W )
  assume iscph.h: |- ., = ( .i ` W )
  assume iscph.n: |- N = ( norm ` W )
  assume iscph.f: |- F = ( Scalar ` W )
  assume iscph.k: |- K = ( Base ` F )

  disjoint W x
  disjoint f k
  disjoint f w
  disjoint F f
  disjoint k w
  disjoint F k
  disjoint F w
  disjoint K f
  disjoint K k
  disjoint K w
  disjoint N f
  disjoint N k
  disjoint N w
  disjoint V f
  disjoint V k
  disjoint V w
  disjoint f x
  disjoint W f
  disjoint k x
  disjoint W k
  disjoint w x
  disjoint W w
  disjoint ., f
  disjoint ., k
  disjoint ., w
  assert |- ( W e. CPreHil <-> ( ( W e. PreHil /\ W e. NrmMod /\ F = ( CCfld |`s K ) ) /\ ( sqrt " ( K i^i ( 0 [,) +oo ) ) ) C_ K /\ N = ( x e. V |-> ( sqrt ` ( x ., x ) ) ) ) )

  proof
    cW
    cphl
    cnlm
    cin
    #
    wcel
    #
    cF
    ccnfld
    cK
    cress
    co
    #
    wceq
    #
    wa
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
    cK
    wss
    #
    cN
    vx
    cV
    vx
    cv
    #
    @9
    c.xi
    co
    #
    csqrt
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    wa
    #
    cW
    cphl
    wcel
    #
    cW
    cnlm
    wcel
    #
    @3
    w3a
    #
    @14
    wa
    cW
    ccph
    wcel
    #
    @18
    @8
    @13
    w3a
    @4
    @18
    @14
    @4
    @16
    @17
    wa
    #
    @3
    wa
    @18
    @1
    @20
    @3
    cW
    cphl
    cnlm
    elin
    anbi1i
    @16
    @17
    @3
    df-3an
    bitr4i
    anbi1i
    @19
    @1
    @3
    @14
    wa
    #
    wa
    @15
    vf
    cv
    #
    ccnfld
    vk
    cv
    #
    cress
    co
    #
    wceq
    #
    csqrt
    @23
    @5
    cin
    #
    cima
    #
    @23
    wss
    #
    vw
    cv
    #
    cnm
    cfv
    #
    vx
    @29
    cbs
    cfv
    #
    @9
    @9
    @29
    cip
    cfv
    #
    co
    #
    csqrt
    cfv
    #
    cmpt
    #
    wceq
    #
    w3a
    #
    vk
    @22
    cbs
    cfv
    #
    wsbc
    #
    vf
    @29
    csca
    cfv
    #
    wsbc
    @21
    vw
    cW
    @0
    ccph
    @29
    cW
    wceq
    #
    @39
    @21
    vf
    @40
    cvv
    @41
    @29
    csca
    fvexd
    @41
    @22
    @40
    wceq
    #
    wa
    #
    @37
    @21
    vk
    @38
    cvv
    @43
    @22
    cbs
    fvexd
    @43
    @23
    @38
    wceq
    #
    wa
    #
    @37
    @3
    @8
    @13
    w3a
    @21
    @45
    @25
    @3
    @28
    @8
    @36
    @13
    @45
    @22
    cF
    @24
    @2
    @45
    @22
    @40
    cF
    @41
    @42
    @44
    simplr
    @45
    @40
    cW
    csca
    cfv
    cF
    @45
    @29
    cW
    csca
    @41
    @42
    @44
    simpll
    #
    fveq2d
    iscph.f
    syl6eqr
    eqtrd
    #
    @45
    @23
    cK
    ccnfld
    cress
    @45
    @23
    @38
    cK
    @43
    @44
    simpr
    @45
    @38
    cF
    cbs
    cfv
    cK
    @45
    @22
    cF
    cbs
    @47
    fveq2d
    iscph.k
    syl6eqr
    eqtrd
    #
    oveq2d
    eqeq12d
    @45
    @27
    @7
    @23
    cK
    @45
    @26
    @6
    csqrt
    @45
    @23
    cK
    @5
    @48
    ineq1d
    imaeq2d
    @48
    sseq12d
    @45
    @30
    cN
    @35
    @12
    @45
    @30
    cW
    cnm
    cfv
    cN
    @45
    @29
    cW
    cnm
    @46
    fveq2d
    iscph.n
    syl6eqr
    @45
    vx
    @31
    @34
    cV
    @11
    @45
    @31
    cW
    cbs
    cfv
    cV
    @45
    @29
    cW
    cbs
    @46
    fveq2d
    iscph.v
    syl6eqr
    @45
    @33
    @10
    csqrt
    @45
    @32
    c.xi
    @9
    @9
    @45
    @32
    cW
    cip
    cfv
    c.xi
    @45
    @29
    cW
    cip
    @46
    fveq2d
    iscph.h
    syl6eqr
    oveqd
    fveq2d
    mpteq12dv
    eqeq12d
    3anbi123d
    @3
    @8
    @13
    3anass
    syl6bb
    sbcied
    sbcied
    vx
    vw
    vf
    vk
    df-cph
    elrab2
    @1
    @3
    @14
    anass
    bitr4i
    @18
    @8
    @13
    3anass
    3bitr4i
end
