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
include "csn.mm"
include "cnei.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cima.mm"
include "wrex.mm"
include "wral.mm"
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
include "elflim.mm"
include "syl2anc.mm"
include "dfss3.mm"
include "cuni.mm"
include "ctop.mm"
include "topontop.mm"
include "eqid.mm"
include "neii1.mm"
include "sylan.mm"
include "wceq.mm"
include "toponuni.mm"
include "adantr.mm"
include "sseqtr4d.mm"
include "elfm.mm"
include "baibd.mm"
include "syldan.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "anbi2d.mm"
include "3bitrd.mm"

theorem flfnei
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s

  disjoint n s
  disjoint F n
  disjoint F s
  disjoint A n
  disjoint J n
  disjoint J s
  disjoint L n
  disjoint L s
  disjoint X n
  disjoint X s
  disjoint Y n
  disjoint Y s
  assert |- ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) -> ( A e. ( ( J fLimf L ) ` F ) <-> ( A e. X /\ A. n e. ( ( nei ` J ) ` { A } ) E. s e. L ( F " s ) C_ n ) ) )

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
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    @5
    wss
    #
    wa
    #
    @8
    cF
    vs
    cv
    cima
    vn
    cv
    #
    wss
    vs
    cL
    wrex
    #
    vn
    @10
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
    @12
    wb
    @0
    @1
    @2
    simp1
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
    @16
    @0
    @1
    @17
    @2
    cX
    cJ
    toponmax
    3ad2ant1
    #
    @1
    @0
    @18
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
    cA
    @5
    cJ
    cX
    elflim
    syl2anc
    @3
    @11
    @15
    @8
    @11
    @13
    @5
    wcel
    #
    vn
    @10
    wral
    @3
    @15
    vn
    @10
    @5
    dfss3
    @3
    @22
    @14
    vn
    @10
    @3
    @13
    @10
    wcel
    #
    @13
    cX
    wss
    #
    @22
    @14
    wb
    @3
    @23
    wa
    @13
    cJ
    cuni
    #
    cX
    @3
    cJ
    ctop
    wcel
    #
    @23
    @13
    @25
    wss
    @0
    @1
    @26
    @2
    cX
    cJ
    topontop
    3ad2ant1
    @9
    cJ
    @13
    @25
    @25
    eqid
    neii1
    sylan
    @3
    cX
    @25
    wceq
    #
    @23
    @0
    @1
    @27
    @2
    cX
    cJ
    toponuni
    3ad2ant1
    adantr
    sseqtr4d
    @3
    @22
    @24
    @14
    @3
    @17
    @18
    @2
    @22
    @24
    @14
    wa
    wb
    @19
    @20
    @21
    vs
    @13
    cL
    cJ
    cF
    cX
    cY
    elfm
    syl3anc
    baibd
    syldan
    ralbidva
    syl5bb
    anbi2d
    3bitrd
end
