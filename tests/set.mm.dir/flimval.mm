include "ctop.mm"
include "wcel.mm"
include "cfil.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "wss.mm"
include "cpw.mm"
include "wa.mm"
include "crab.mm"
include "cvv.mm"
include "cflim.mm"
include "co.mm"
include "wceq.mm"
include "topopn.mm"
include "adantr.mm"
include "rabexg.mm"
include "syl.mm"
include "simpl.mm"
include "unieqd.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "simpr.mm"
include "sseq12d.mm"
include "pweqd.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "df-flim.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"

theorem flimval
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let cX: class X
  let cA: class A
  let vf: setvar f
  let vj: setvar j
  assume flimval.1: |- X = U. J

  disjoint F x
  disjoint J x
  disjoint X x
  disjoint A x
  disjoint f j
  disjoint f x
  disjoint F f
  disjoint j x
  disjoint F j
  disjoint J f
  disjoint J j
  disjoint X f
  disjoint X j
  assert |- ( ( J e. Top /\ F e. U. ran Fil ) -> ( J fLim F ) = { x e. X | ( ( ( nei ` J ) ` { x } ) C_ F /\ F C_ ~P X ) } )

  proof
    cJ
    ctop
    wcel
    #
    cF
    cfil
    crn
    cuni
    #
    wcel
    #
    vx
    cv
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
    cF
    wss
    #
    cF
    cX
    cpw
    #
    wss
    #
    wa
    #
    vx
    cX
    crab
    #
    cvv
    wcel
    #
    cJ
    cF
    cflim
    co
    @10
    wceq
    @0
    @2
    wa
    cX
    cJ
    wcel
    #
    @11
    @0
    @12
    @2
    cJ
    cX
    flimval.1
    topopn
    adantr
    @9
    vx
    cX
    cJ
    rabexg
    syl
    vj
    vf
    cJ
    cF
    ctop
    @1
    @3
    vj
    cv
    #
    cnei
    cfv
    #
    cfv
    #
    vf
    cv
    #
    wss
    #
    @16
    @13
    cuni
    #
    cpw
    #
    wss
    #
    wa
    #
    vx
    @18
    crab
    @10
    cflim
    cvv
    @13
    cJ
    wceq
    #
    @16
    cF
    wceq
    #
    wa
    #
    @21
    @9
    vx
    @18
    cX
    @24
    @18
    cJ
    cuni
    cX
    @24
    @13
    cJ
    @22
    @23
    simpl
    #
    unieqd
    flimval.1
    syl6eqr
    #
    @24
    @17
    @6
    @20
    @8
    @24
    @15
    @5
    @16
    cF
    @24
    @3
    @14
    @4
    @24
    @13
    cJ
    cnei
    @25
    fveq2d
    fveq1d
    @22
    @23
    simpr
    #
    sseq12d
    @24
    @16
    cF
    @19
    @7
    @27
    @24
    @18
    cX
    @26
    pweqd
    sseq12d
    anbi12d
    rabeqbidv
    vx
    vf
    vj
    df-flim
    ovmpt2ga
    mpd3an3
end
