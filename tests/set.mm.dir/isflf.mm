include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "w3a.mm"
include "cflf.mm"
include "co.mm"
include "cfm.mm"
include "cflim.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "flfval.mm"
include "eleq2d.mm"
include "wb.mm"
include "simp1.mm"
include "cfbas.mm"
include "toponmax.mm"
include "3ad2ant1.mm"
include "filfbas.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "fmfil.mm"
include "syl3anc.mm"
include "flimopn.mm"
include "syl2anc.mm"
include "elfm.mm"
include "adantr.mm"
include "toponss.mm"
include "sylan.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "anbi2d.mm"
include "3bitrd.mm"

theorem isflf
  let cA: class A
  let vo: setvar o
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s

  disjoint A o
  disjoint o s
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
  assert |- ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) -> ( A e. ( ( J fLimf L ) ` F ) <-> ( A e. X /\ A. o e. J ( A e. o -> E. s e. L ( F " s ) C_ o ) ) ) )

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
    #
    wcel
    cA
    cJ
    cL
    cX
    cF
    cfm
    co
    cfv
    #
    cflim
    co
    #
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
    @9
    @5
    wcel
    #
    wi
    #
    vo
    cJ
    wral
    #
    wa
    #
    @8
    @10
    cF
    vs
    cv
    cima
    @9
    wss
    vs
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
    @3
    @4
    @6
    cA
    cF
    cJ
    cL
    cX
    cY
    flfval
    eleq2d
    @3
    @0
    @5
    cX
    cfil
    cfv
    wcel
    #
    @7
    @14
    wb
    @0
    @1
    @2
    simp1
    #
    @3
    cX
    cJ
    wcel
    #
    cL
    cY
    cfbas
    cfv
    wcel
    #
    @2
    @18
    @0
    @1
    @20
    @2
    cX
    cJ
    toponmax
    3ad2ant1
    #
    @1
    @0
    @21
    @2
    cL
    cY
    filfbas
    3ad2ant2
    #
    @0
    @1
    @2
    simp3
    #
    cJ
    cL
    cF
    cX
    cY
    fmfil
    syl3anc
    vo
    cA
    @5
    cJ
    cX
    flimopn
    syl2anc
    @3
    @13
    @17
    @8
    @3
    @12
    @16
    vo
    cJ
    @3
    @9
    cJ
    wcel
    #
    wa
    #
    @11
    @15
    @10
    @26
    @11
    @9
    cX
    wss
    #
    @15
    wa
    #
    @15
    @3
    @11
    @28
    wb
    #
    @25
    @3
    @20
    @21
    @2
    @29
    @22
    @23
    @24
    vs
    @9
    cL
    cJ
    cF
    cX
    cY
    elfm
    syl3anc
    adantr
    @26
    @27
    @15
    @3
    @0
    @25
    @27
    @19
    @9
    cJ
    cX
    toponss
    sylan
    biantrurd
    bitr4d
    imbi2d
    ralbidva
    anbi2d
    3bitrd
end
