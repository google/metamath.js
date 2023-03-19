include "wcel.mm"
include "wfo.mm"
include "wss.mm"
include "w3a.mm"
include "cqtop.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cin.mm"
include "cpw.mm"
include "crab.mm"
include "cvv.mm"
include "wceq.mm"
include "simp1.mm"
include "wf.mm"
include "fof.mm"
include "3ad2ant2.mm"
include "cuni.mm"
include "uniexg.mm"
include "3ad2ant1.mm"
include "syl5eqel.mm"
include "simp3.mm"
include "ssexd.mm"
include "fex.mm"
include "syl2anc.mm"
include "qtopval.mm"
include "crn.mm"
include "imassrn.mm"
include "forn.mm"
include "syl5sseq.mm"
include "foima.mm"
include "imass2.mm"
include "syl.mm"
include "eqsstr3d.mm"
include "eqssd.mm"
include "pweqd.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "sstrd.mm"
include "df-ss.mm"
include "sylib.mm"
include "eleq1d.mm"
include "rabeqbidv.mm"
include "eqtrd.mm"

theorem qtopval2
  let cF: class F
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let cA: class A
  let vf: setvar f
  let vj: setvar j
  assume qtopval.1: |- X = U. J

  disjoint F s
  disjoint J s
  disjoint V s
  disjoint Y s
  disjoint Z s
  disjoint X s
  disjoint A s
  disjoint f j
  disjoint f s
  disjoint F f
  disjoint j s
  disjoint F j
  disjoint J f
  disjoint J j
  disjoint X f
  disjoint X j
  assert |- ( ( J e. V /\ F : Z -onto-> Y /\ Z C_ X ) -> ( J qTop F ) = { s e. ~P Y | ( `' F " s ) e. J } )

  proof
    cJ
    cV
    wcel
    #
    cZ
    cY
    cF
    wfo
    #
    cZ
    cX
    wss
    #
    w3a
    #
    cJ
    cF
    cqtop
    co
    #
    cF
    ccnv
    vs
    cv
    #
    cima
    #
    cX
    cin
    #
    cJ
    wcel
    #
    vs
    cF
    cX
    cima
    #
    cpw
    #
    crab
    #
    @6
    cJ
    wcel
    #
    vs
    cY
    cpw
    #
    crab
    @3
    @0
    cF
    cvv
    wcel
    #
    @4
    @11
    wceq
    @0
    @1
    @2
    simp1
    @3
    cZ
    cY
    cF
    wf
    #
    cZ
    cvv
    wcel
    @14
    @1
    @0
    @15
    @2
    cZ
    cY
    cF
    fof
    3ad2ant2
    #
    @3
    cZ
    cX
    cvv
    @3
    cX
    cJ
    cuni
    #
    cvv
    qtopval.1
    @0
    @1
    @17
    cvv
    wcel
    @2
    cJ
    cV
    uniexg
    3ad2ant1
    syl5eqel
    @0
    @1
    @2
    simp3
    #
    ssexd
    cZ
    cY
    cvv
    cF
    fex
    syl2anc
    cF
    cJ
    cV
    cvv
    cX
    vs
    qtopval.1
    qtopval
    syl2anc
    @3
    @8
    @12
    vs
    @10
    @13
    @3
    @9
    cY
    @3
    @9
    cY
    @3
    cF
    crn
    #
    @9
    cY
    cF
    cX
    imassrn
    @1
    @0
    @19
    cY
    wceq
    @2
    cZ
    cY
    cF
    forn
    3ad2ant2
    syl5sseq
    @3
    cY
    cF
    cZ
    cima
    #
    @9
    @1
    @0
    @20
    cY
    wceq
    @2
    cZ
    cY
    cF
    foima
    3ad2ant2
    @3
    @2
    @20
    @9
    wss
    @18
    cZ
    cX
    cF
    imass2
    syl
    eqsstr3d
    eqssd
    pweqd
    @3
    @7
    @6
    cJ
    @3
    @6
    cX
    wss
    @7
    @6
    wceq
    @3
    @6
    cZ
    cX
    @3
    cF
    cdm
    #
    @6
    cZ
    cF
    @5
    cnvimass
    @3
    @15
    @21
    cZ
    wceq
    @16
    cZ
    cY
    cF
    fdm
    syl
    syl5sseq
    @18
    sstrd
    @6
    cX
    df-ss
    sylib
    eleq1d
    rabeqbidv
    eqtrd
end
