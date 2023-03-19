include "ctop.mm"
include "wcel.mm"
include "cfil.mm"
include "crn.mm"
include "cuni.mm"
include "wa.mm"
include "cpw.mm"
include "wss.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "w3a.mm"
include "cflim.mm"
include "co.mm"
include "anass.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "cv.mm"
include "crab.mm"
include "df-flim.mm"
include "elmpt2cl.mm"
include "flimval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "sneq.mm"
include "fveq2d.mm"
include "sseq1d.mm"
include "anbi1d.mm"
include "ancom.mm"
include "syl6bb.mm"
include "elrab.mm"
include "an12.mm"
include "bitri.mm"
include "biadan2.mm"
include "3bitr4ri.mm"

theorem elflim2
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vf: setvar f
  let vj: setvar j
  assume flimval.1: |- X = U. J


  assert |- ( A e. ( J fLim F ) <-> ( ( J e. Top /\ F e. U. ran Fil /\ F C_ ~P X ) /\ ( A e. X /\ ( ( nei ` J ) ` { A } ) C_ F ) ) )

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
    wa
    #
    cF
    cX
    cpw
    wss
    #
    wa
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
    #
    cfv
    #
    cF
    wss
    #
    wa
    #
    wa
    @3
    @4
    @11
    wa
    #
    wa
    @0
    @2
    @4
    w3a
    #
    @11
    wa
    cA
    cJ
    cF
    cflim
    co
    #
    wcel
    #
    @3
    @4
    @11
    anass
    @13
    @5
    @11
    @0
    @2
    @4
    df-3an
    anbi1i
    @15
    @3
    @12
    vj
    vf
    ctop
    @1
    vx
    cv
    #
    csn
    #
    vj
    cv
    #
    cnei
    cfv
    cfv
    vf
    cv
    #
    wss
    @19
    @18
    cuni
    #
    cpw
    wss
    wa
    vx
    @20
    crab
    cJ
    cF
    cflim
    cA
    vx
    vf
    vj
    df-flim
    elmpt2cl
    @3
    @15
    cA
    @17
    @8
    cfv
    #
    cF
    wss
    #
    @4
    wa
    #
    vx
    cX
    crab
    #
    wcel
    #
    @12
    @3
    @14
    @24
    cA
    vx
    cF
    cJ
    cX
    flimval.1
    flimval
    eleq2d
    @25
    @6
    @4
    @10
    wa
    #
    wa
    @12
    @23
    @26
    vx
    cA
    cX
    @16
    cA
    wceq
    #
    @23
    @10
    @4
    wa
    @26
    @27
    @22
    @10
    @4
    @27
    @21
    @9
    cF
    @27
    @17
    @7
    @8
    @16
    cA
    sneq
    fveq2d
    sseq1d
    anbi1d
    @10
    @4
    ancom
    syl6bb
    elrab
    @6
    @4
    @10
    an12
    bitri
    syl6bb
    biadan2
    3bitr4ri
end
