include "wcel.mm"
include "cvv.mm"
include "cqtop.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cin.mm"
include "cpw.mm"
include "crab.mm"
include "wceq.mm"
include "elex.mm"
include "imaexg.mm"
include "pwexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "adantl.mm"
include "cuni.mm"
include "wa.mm"
include "simpr.mm"
include "simpl.mm"
include "unieqd.mm"
include "syl6eqr.mm"
include "imaeq12d.mm"
include "pweqd.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "ineq12d.mm"
include "eleq12d.mm"
include "rabeqbidv.mm"
include "df-qtop.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"
include "syl2an.mm"

theorem qtopval
  let cF: class F
  let cJ: class J
  let cV: class V
  let cW: class W
  let cX: class X
  let vs: setvar s
  let cA: class A
  let vf: setvar f
  let vj: setvar j
  let cY: class Y
  let cZ: class Z
  assume qtopval.1: |- X = U. J

  disjoint F s
  disjoint J s
  disjoint V s
  disjoint X s
  disjoint A s
  disjoint f j
  disjoint f s
  disjoint F f
  disjoint j s
  disjoint F j
  disjoint J f
  disjoint J j
  disjoint Y s
  disjoint Z s
  disjoint X f
  disjoint X j
  assert |- ( ( J e. V /\ F e. W ) -> ( J qTop F ) = { s e. ~P ( F " X ) | ( ( `' F " s ) i^i X ) e. J } )

  proof
    cJ
    cV
    wcel
    cJ
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    cJ
    cF
    cqtop
    co
    cF
    ccnv
    #
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
    wceq
    #
    cF
    cW
    wcel
    cJ
    cV
    elex
    cF
    cW
    elex
    @0
    @1
    @9
    cvv
    wcel
    #
    @10
    @1
    @11
    @0
    @1
    @7
    cvv
    wcel
    @8
    cvv
    wcel
    @11
    cF
    cX
    cvv
    imaexg
    @7
    cvv
    pwexg
    @6
    vs
    @8
    cvv
    rabexg
    3syl
    adantl
    vj
    vf
    cJ
    cF
    cvv
    cvv
    vf
    cv
    #
    ccnv
    #
    @3
    cima
    #
    vj
    cv
    #
    cuni
    #
    cin
    #
    @15
    wcel
    #
    vs
    @12
    @16
    cima
    #
    cpw
    #
    crab
    @9
    cqtop
    cvv
    @15
    cJ
    wceq
    #
    @12
    cF
    wceq
    #
    wa
    #
    @18
    @6
    vs
    @20
    @8
    @23
    @19
    @7
    @23
    @12
    cF
    @16
    cX
    @21
    @22
    simpr
    #
    @23
    @16
    cJ
    cuni
    cX
    @23
    @15
    cJ
    @21
    @22
    simpl
    #
    unieqd
    qtopval.1
    syl6eqr
    #
    imaeq12d
    pweqd
    @23
    @17
    @5
    @15
    cJ
    @23
    @14
    @4
    @16
    cX
    @23
    @13
    @2
    @3
    @23
    @12
    cF
    @24
    cnveqd
    imaeq1d
    @26
    ineq12d
    @25
    eleq12d
    rabeqbidv
    vf
    vj
    vs
    df-qtop
    ovmpt2ga
    mpd3an3
    syl2an
end
