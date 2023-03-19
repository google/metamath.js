include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
include "wa.mm"
include "cfcls.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wi.mm"
include "cfil.mm"
include "wb.mm"
include "cfg.mm"
include "fgcl.mm"
include "adantl.mm"
include "syl5eqel.mm"
include "fclsopn.mm"
include "syldan.mm"
include "wss.mm"
include "ssfg.mm"
include "ad3antlr.mm"
include "syl6sseqr.mm"
include "ssralv.mm"
include "syl.mm"
include "weq.mm"
include "ineq2.mm"
include "neeq1d.mm"
include "cbvralv.mm"
include "syl6ib.mm"
include "wrex.mm"
include "eleq2i.mm"
include "elfg.mm"
include "syl5bb.mm"
include "simplbda.mm"
include "r19.29r.mm"
include "sslin.mm"
include "ssn0.mm"
include "sylan.mm"
include "rexlimivw.mm"
include "ex.mm"
include "ralrimdva.mm"
include "impbid.mm"
include "anassrs.mm"
include "pm5.74da.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem fclsbas
  let cA: class A
  let cB: class B
  let vo: setvar o
  let cF: class F
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  assume fclsbas.f: |- F = ( X filGen B )

  disjoint A o
  disjoint o s
  disjoint B o
  disjoint B s
  disjoint F o
  disjoint J o
  disjoint X o
  disjoint o t
  disjoint A t
  disjoint s t
  disjoint B t
  disjoint F t
  disjoint J t
  disjoint X t
  assert |- ( ( J e. ( TopOn ` X ) /\ B e. ( fBas ` X ) ) -> ( A e. ( J fClus F ) <-> ( A e. X /\ A. o e. J ( A e. o -> A. s e. B ( o i^i s ) =/= (/) ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cB
    cX
    cfbas
    cfv
    wcel
    #
    wa
    #
    cA
    cJ
    cF
    cfcls
    co
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    vo
    cv
    #
    wcel
    #
    @5
    vt
    cv
    #
    cin
    #
    c0
    wne
    #
    vt
    cF
    wral
    #
    wi
    #
    vo
    cJ
    wral
    #
    wa
    #
    @4
    @6
    @5
    vs
    cv
    #
    cin
    #
    c0
    wne
    #
    vs
    cB
    wral
    #
    wi
    #
    vo
    cJ
    wral
    #
    wa
    @0
    @1
    cF
    cX
    cfil
    cfv
    #
    wcel
    @3
    @13
    wb
    @2
    cF
    cX
    cB
    cfg
    co
    #
    @20
    fclsbas.f
    @1
    @21
    @20
    wcel
    @0
    cB
    cX
    fgcl
    adantl
    syl5eqel
    cA
    vo
    cF
    cJ
    cX
    vt
    fclsopn
    syldan
    @2
    @4
    @12
    @19
    @2
    @4
    wa
    #
    @11
    @18
    vo
    cJ
    @22
    @5
    cJ
    wcel
    #
    wa
    @6
    @10
    @17
    @22
    @23
    @6
    @10
    @17
    wb
    @22
    @23
    @6
    wa
    #
    wa
    #
    @10
    @17
    @25
    @10
    @9
    vt
    cB
    wral
    #
    @17
    @25
    cB
    cF
    wss
    @10
    @26
    wi
    @25
    cB
    @21
    cF
    @1
    cB
    @21
    wss
    @0
    @4
    @24
    cB
    cX
    ssfg
    ad3antlr
    fclsbas.f
    syl6sseqr
    @9
    vt
    cB
    cF
    ssralv
    syl
    @9
    @16
    vt
    vs
    cB
    vt
    vs
    weq
    @8
    @15
    c0
    @7
    @14
    @5
    ineq2
    neeq1d
    cbvralv
    syl6ib
    @25
    @17
    @9
    vt
    cF
    @25
    @7
    cF
    wcel
    #
    wa
    @14
    @7
    wss
    #
    vs
    cB
    wrex
    #
    @17
    @9
    wi
    @25
    @27
    @7
    cX
    wss
    #
    @29
    @27
    @7
    @21
    wcel
    #
    @25
    @30
    @29
    wa
    #
    cF
    @21
    @7
    fclsbas.f
    eleq2i
    @1
    @31
    @32
    wb
    @0
    @4
    @24
    vs
    @7
    cB
    cX
    elfg
    ad3antlr
    syl5bb
    simplbda
    @29
    @17
    @9
    @29
    @17
    wa
    @28
    @16
    wa
    #
    vs
    cB
    wrex
    @9
    @28
    @16
    vs
    cB
    r19.29r
    @33
    @9
    vs
    cB
    @28
    @15
    @8
    wss
    @16
    @9
    @14
    @7
    @5
    sslin
    @15
    @8
    ssn0
    sylan
    rexlimivw
    syl
    ex
    syl
    ralrimdva
    impbid
    anassrs
    pm5.74da
    ralbidva
    pm5.32da
    bitrd
end
