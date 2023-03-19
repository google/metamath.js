include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "w3a.mm"
include "cflf.mm"
include "co.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "isflf.mm"
include "ctg.mm"
include "raleqi.mm"
include "ctb.mm"
include "ctop.mm"
include "simpl1.mm"
include "topontop.mm"
include "syl.mm"
include "syl5eqelr.mm"
include "tgclb.mm"
include "sylibr.mm"
include "bastg.mm"
include "weq.mm"
include "eleq2.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "ssralv.mm"
include "syl5bi.mm"
include "3syl.mm"
include "tg2.mm"
include "r19.29.mm"
include "simpl.mm"
include "simpr.mm"
include "sstr2.mm"
include "syl5com.mm"
include "reximdv.mm"
include "embantd.mm"
include "impcom.mm"
include "rexlimivw.mm"
include "ex.mm"
include "syl5.mm"
include "expdimp.mm"
include "ralrimiva.mm"
include "impbid1.mm"
include "syl5bb.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem flftg
  let cA: class A
  let cB: class B
  let vo: setvar o
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vu: setvar u
  assume flftg.l: |- J = ( topGen ` B )

  disjoint o s
  disjoint A o
  disjoint A s
  disjoint B o
  disjoint F o
  disjoint F s
  disjoint J s
  disjoint L o
  disjoint L s
  disjoint X s
  disjoint Y s
  disjoint o u
  disjoint s u
  disjoint A u
  disjoint B u
  disjoint F u
  disjoint J u
  disjoint L u
  disjoint X u
  disjoint Y u
  assert |- ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) -> ( A e. ( ( J fLimf L ) ` F ) <-> ( A e. X /\ A. o e. B ( A e. o -> E. s e. L ( F " s ) C_ o ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cL
    cY
    cfil
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cA
    cF
    cJ
    cL
    cflf
    co
    cfv
    wcel
    cA
    cX
    wcel
    #
    cA
    vu
    cv
    #
    wcel
    #
    cF
    vs
    cv
    cima
    #
    @5
    wss
    #
    vs
    cL
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    wa
    @4
    cA
    vo
    cv
    #
    wcel
    #
    @7
    @12
    wss
    #
    vs
    cL
    wrex
    #
    wi
    #
    vo
    cB
    wral
    #
    wa
    cA
    vu
    cF
    cJ
    cL
    cX
    cY
    vs
    isflf
    @3
    @4
    @11
    @17
    @11
    @10
    vu
    cB
    ctg
    cfv
    #
    wral
    #
    @3
    @4
    wa
    #
    @17
    @10
    vu
    cJ
    @18
    flftg.l
    raleqi
    @20
    @19
    @17
    @20
    cB
    ctb
    wcel
    #
    cB
    @18
    wss
    #
    @19
    @17
    wi
    @20
    @18
    ctop
    wcel
    @21
    @20
    @18
    cJ
    ctop
    flftg.l
    @20
    @0
    cJ
    ctop
    wcel
    @0
    @1
    @2
    @4
    simpl1
    cX
    cJ
    topontop
    syl
    syl5eqelr
    cB
    tgclb
    sylibr
    cB
    ctb
    bastg
    @19
    @16
    vo
    @18
    wral
    @22
    @17
    @10
    @16
    vu
    vo
    @18
    vu
    vo
    weq
    #
    @6
    @13
    @9
    @15
    @5
    @12
    cA
    eleq2
    @23
    @8
    @14
    vs
    cL
    @5
    @12
    @7
    sseq2
    rexbidv
    imbi12d
    cbvralv
    @16
    vo
    cB
    @18
    ssralv
    syl5bi
    3syl
    @17
    @10
    vu
    @18
    @17
    @5
    @18
    wcel
    #
    @6
    @9
    @24
    @6
    wa
    @13
    @12
    @5
    wss
    #
    wa
    #
    vo
    cB
    wrex
    #
    @17
    @9
    vo
    @5
    cB
    cA
    tg2
    @17
    @27
    @9
    @17
    @27
    wa
    @16
    @26
    wa
    #
    vo
    cB
    wrex
    @9
    @16
    @26
    vo
    cB
    r19.29
    @28
    @9
    vo
    cB
    @26
    @16
    @9
    @26
    @13
    @15
    @9
    @13
    @25
    simpl
    @26
    @14
    @8
    vs
    cL
    @26
    @25
    @14
    @8
    @13
    @25
    simpr
    @7
    @12
    @5
    sstr2
    syl5com
    reximdv
    embantd
    impcom
    rexlimivw
    syl
    ex
    syl5
    expdimp
    ralrimiva
    impbid1
    syl5bb
    pm5.32da
    bitrd
end
