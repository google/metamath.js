include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wss.mm"
include "cv.mm"
include "cdm.mm"
include "ccl.mm"
include "cfv.mm"
include "csn.mm"
include "cnei.mm"
include "crest.mm"
include "co.mm"
include "cflf.mm"
include "cxp.mm"
include "ciun.mm"
include "cuni.mm"
include "cpm.mm"
include "ccnext.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "cnextval.mm"
include "adantr.mm"
include "simpr.mm"
include "dmeqd.mm"
include "simplrl.mm"
include "fdm.mm"
include "syl.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "fveq12d.mm"
include "xpeq2d.mm"
include "iuneq12d.mm"
include "uniexg.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "feq23i.mm"
include "biimpi.mm"
include "ad2antrl.mm"
include "sseq2i.mm"
include "ad2antll.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "fvex.mm"
include "snex.mm"
include "xpex.mm"
include "iunex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem cnextfval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  assume cnextfval.1: |- X = U. J
  assume cnextfval.2: |- B = U. K

  disjoint J x
  disjoint K x
  disjoint A x
  disjoint B x
  disjoint F x
  disjoint X x
  disjoint f j
  disjoint f k
  disjoint f x
  disjoint J f
  disjoint j k
  disjoint j x
  disjoint J j
  disjoint k x
  disjoint J k
  disjoint K f
  disjoint K j
  disjoint K k
  disjoint A f
  disjoint B f
  disjoint F f
  disjoint X f
  assert |- ( ( ( J e. Top /\ K e. Top ) /\ ( F : A --> B /\ A C_ X ) ) -> ( ( J CnExt K ) ` F ) = U_ x e. ( ( cls ` J ) ` A ) ( { x } X. ( ( K fLimf ( ( ( nei ` J ) ` { x } ) |`t A ) ) ` F ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    wa
    #
    cA
    cB
    cF
    wf
    #
    cA
    cX
    wss
    #
    wa
    #
    wa
    #
    vf
    cF
    vx
    vf
    cv
    #
    cdm
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    vx
    cv
    #
    csn
    #
    @7
    cK
    @12
    cJ
    cnei
    cfv
    cfv
    #
    @8
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    cxp
    #
    ciun
    #
    vx
    cA
    @9
    cfv
    #
    @12
    cF
    cK
    @13
    cA
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    cxp
    #
    ciun
    #
    cK
    cuni
    #
    cJ
    cuni
    #
    cpm
    co
    #
    cJ
    cK
    ccnext
    co
    #
    cvv
    @2
    @28
    vf
    @27
    @18
    cmpt
    wceq
    @5
    vx
    vf
    cJ
    cK
    cnextval
    adantr
    @6
    @7
    cF
    wceq
    #
    wa
    #
    vx
    @10
    @19
    @17
    @23
    @30
    @8
    cA
    @9
    @30
    @8
    cF
    cdm
    #
    cA
    @30
    @7
    cF
    @6
    @29
    simpr
    #
    dmeqd
    @30
    @3
    @31
    cA
    wceq
    @2
    @3
    @4
    @29
    simplrl
    cA
    cB
    cF
    fdm
    syl
    eqtrd
    #
    fveq2d
    @30
    @16
    @22
    @12
    @30
    @7
    cF
    @15
    @21
    @30
    @14
    @20
    cK
    cflf
    @30
    @8
    cA
    @13
    crest
    @33
    oveq2d
    oveq2d
    @32
    fveq12d
    xpeq2d
    iuneq12d
    @6
    @25
    cvv
    wcel
    #
    @26
    cvv
    wcel
    #
    cA
    @25
    cF
    wf
    #
    cA
    @26
    wss
    #
    cF
    @27
    wcel
    @1
    @34
    @0
    @5
    cK
    ctop
    uniexg
    ad2antlr
    @0
    @35
    @1
    @5
    cJ
    ctop
    uniexg
    ad2antrr
    @3
    @36
    @2
    @4
    @3
    @36
    cA
    cB
    cA
    @25
    cF
    cA
    eqid
    cnextfval.2
    feq23i
    biimpi
    ad2antrl
    @4
    @37
    @2
    @3
    @4
    @37
    cX
    @26
    cA
    cnextfval.1
    sseq2i
    biimpi
    ad2antll
    @25
    @26
    cA
    cF
    cvv
    cvv
    elpm2r
    syl22anc
    @24
    cvv
    wcel
    @6
    vx
    @19
    @23
    cA
    @9
    fvex
    @12
    @22
    @11
    snex
    cF
    @21
    fvex
    xpex
    iunex
    a1i
    fvmptd
end
