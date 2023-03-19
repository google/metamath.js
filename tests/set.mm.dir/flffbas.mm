include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
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
include "cfil.mm"
include "wb.mm"
include "cfg.mm"
include "fgcl.mm"
include "syl5eqel.mm"
include "isflf.mm"
include "syl3an2.mm"
include "eleq2i.mm"
include "elfg.mm"
include "3ad2ant2.mm"
include "sstr2.mm"
include "imass2.mm"
include "syl11.mm"
include "adantl.mm"
include "reximdv.mm"
include "ex.mm"
include "com23.mm"
include "adantld.mm"
include "sylbid.mm"
include "adantr.mm"
include "syl5bi.mm"
include "rexlimdv.mm"
include "ssfg.mm"
include "syl6sseqr.mm"
include "sselda.mm"
include "3ad2antl2.mm"
include "ad2ant2r.mm"
include "simprr.mm"
include "weq.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdvaa.mm"
include "impbid.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem flffbas
  let cA: class A
  let cB: class B
  let vo: setvar o
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  assume flffbas.l: |- L = ( Y filGen B )

  disjoint o s
  disjoint A o
  disjoint A s
  disjoint B o
  disjoint B s
  disjoint F o
  disjoint F s
  disjoint J o
  disjoint J s
  disjoint L o
  disjoint L s
  disjoint X o
  disjoint X s
  disjoint Y o
  disjoint Y s
  disjoint o t
  disjoint s t
  disjoint A t
  disjoint B t
  disjoint F t
  disjoint J t
  disjoint L t
  disjoint X t
  disjoint Y t
  assert |- ( ( J e. ( TopOn ` X ) /\ B e. ( fBas ` Y ) /\ F : Y --> X ) -> ( A e. ( ( J fLimf L ) ` F ) <-> ( A e. X /\ A. o e. J ( A e. o -> E. s e. B ( F " s ) C_ o ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cB
    cY
    cfbas
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
    cF
    vt
    cv
    #
    cima
    #
    @6
    wss
    #
    vt
    cL
    wrex
    #
    wi
    #
    vo
    cJ
    wral
    #
    wa
    #
    @5
    @7
    cF
    vs
    cv
    #
    cima
    #
    @6
    wss
    #
    vs
    cB
    wrex
    #
    wi
    #
    vo
    cJ
    wral
    #
    wa
    @1
    @0
    cL
    cY
    cfil
    cfv
    #
    wcel
    @2
    @4
    @14
    wb
    @1
    cL
    cY
    cB
    cfg
    co
    #
    @21
    flffbas.l
    cB
    cY
    fgcl
    syl5eqel
    cA
    vo
    cF
    cJ
    cL
    cX
    cY
    vt
    isflf
    syl3an2
    @3
    @5
    @13
    @20
    @3
    @5
    wa
    #
    @12
    @19
    vo
    cJ
    @23
    @11
    @18
    @7
    @23
    @11
    @18
    @23
    @10
    @18
    vt
    cL
    @8
    cL
    wcel
    @8
    @22
    wcel
    #
    @23
    @10
    @18
    wi
    #
    cL
    @22
    @8
    flffbas.l
    eleq2i
    @3
    @24
    @25
    wi
    @5
    @3
    @24
    @8
    cY
    wss
    #
    @15
    @8
    wss
    #
    vs
    cB
    wrex
    #
    wa
    #
    @25
    @1
    @0
    @24
    @29
    wb
    @2
    vs
    @8
    cB
    cY
    elfg
    3ad2ant2
    @3
    @28
    @25
    @26
    @3
    @10
    @28
    @18
    @3
    @10
    @28
    @18
    wi
    @3
    @10
    wa
    @27
    @17
    vs
    cB
    @10
    @27
    @17
    wi
    @3
    @16
    @9
    wss
    @10
    @17
    @27
    @16
    @9
    @6
    sstr2
    @15
    @8
    cF
    imass2
    syl11
    adantl
    reximdv
    ex
    com23
    adantld
    sylbid
    adantr
    syl5bi
    rexlimdv
    @23
    @17
    @11
    vs
    cB
    @23
    @15
    cB
    wcel
    #
    @17
    wa
    wa
    @15
    cL
    wcel
    #
    @17
    @11
    @3
    @30
    @31
    @5
    @17
    @1
    @0
    @30
    @31
    @2
    @1
    cB
    cL
    @15
    @1
    cB
    @22
    cL
    cB
    cY
    ssfg
    flffbas.l
    syl6sseqr
    sselda
    3ad2antl2
    ad2ant2r
    @23
    @30
    @17
    simprr
    @10
    @17
    vt
    @15
    cL
    vt
    vs
    weq
    @9
    @16
    @6
    @8
    @15
    cF
    imaeq2
    sseq1d
    rspcev
    syl2anc
    rexlimdvaa
    impbid
    imbi2d
    ralbidv
    pm5.32da
    bitrd
end
