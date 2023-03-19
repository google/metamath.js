include "wcel.mm"
include "cr1.mm"
include "cfv.mm"
include "cwun.mm"
include "wlim.mm"
include "wa.mm"
include "word.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "con0.mm"
include "wrex.mm"
include "wo.mm"
include "wn.mm"
include "cdm.mm"
include "simpr.mm"
include "wun0.mm"
include "elfvdm.mm"
include "syl.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "syl6eleq.mm"
include "eloni.mm"
include "n0i.mm"
include "fveq2.mm"
include "r10.mm"
include "syl6eq.mm"
include "nsyl.mm"
include "cima.mm"
include "cuni.mm"
include "suceloni.mm"
include "sucidg.mm"
include "r1ord.mm"
include "sylc.mm"
include "r1elwf.mm"
include "wfelirr.mm"
include "3syl.mm"
include "cpw.mm"
include "simprr.mm"
include "fveq2d.mm"
include "r1suc.mm"
include "ad2antrl.mm"
include "eqtrd.mm"
include "simplr.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "wunpw.mm"
include "eqeltrd.mm"
include "rexlimdvaa.mm"
include "mtod.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "dflim3.mm"
include "r1limwun.mm"
include "impbida.mm"

theorem r1wunlim
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> ( ( R1 ` A ) e. WUni <-> Lim A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cr1
    cfv
    #
    cwun
    wcel
    #
    cA
    wlim
    #
    @0
    @2
    wa
    #
    cA
    word
    #
    cA
    c0
    wceq
    #
    cA
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    wo
    wn
    #
    @3
    @4
    cA
    con0
    wcel
    #
    @5
    @4
    cA
    cr1
    cdm
    #
    con0
    @4
    c0
    @1
    wcel
    #
    cA
    @13
    wcel
    @4
    @1
    @0
    @2
    simpr
    wun0
    #
    c0
    cA
    cr1
    elfvdm
    syl
    cr1
    con0
    wfn
    @13
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    syl6eleq
    #
    cA
    eloni
    syl
    @4
    @6
    wn
    @10
    wn
    @11
    @4
    @1
    c0
    wceq
    #
    @6
    @4
    @14
    @17
    wn
    @15
    @1
    c0
    n0i
    syl
    @6
    @1
    c0
    cr1
    cfv
    c0
    cA
    c0
    cr1
    fveq2
    r10
    syl6eq
    nsyl
    @4
    @10
    @1
    @1
    wcel
    #
    @4
    @1
    cA
    csuc
    #
    cr1
    cfv
    wcel
    #
    @1
    cr1
    con0
    cima
    cuni
    wcel
    @18
    wn
    @4
    @19
    con0
    wcel
    #
    cA
    @19
    wcel
    #
    @20
    @4
    @12
    @21
    @16
    cA
    suceloni
    syl
    @4
    @12
    @22
    @16
    cA
    con0
    sucidg
    syl
    cA
    @19
    r1ord
    sylc
    @1
    @19
    r1elwf
    @1
    wfelirr
    3syl
    @4
    @9
    @18
    vx
    con0
    @4
    @7
    con0
    wcel
    #
    @9
    wa
    #
    wa
    #
    @1
    @7
    cr1
    cfv
    #
    cpw
    #
    @1
    @25
    @1
    @8
    cr1
    cfv
    #
    @27
    @25
    cA
    @8
    cr1
    @4
    @23
    @9
    simprr
    #
    fveq2d
    @23
    @28
    @27
    wceq
    @4
    @9
    @7
    r1suc
    ad2antrl
    eqtrd
    @25
    @26
    @1
    @0
    @2
    @24
    simplr
    @25
    @12
    @7
    cA
    wcel
    @26
    @1
    wcel
    @4
    @12
    @24
    @16
    adantr
    @25
    @7
    @8
    cA
    @23
    @7
    @8
    wcel
    @4
    @9
    @7
    con0
    sucidg
    ad2antrl
    @29
    eleqtrrd
    @7
    cA
    r1ord
    sylc
    wunpw
    eqeltrd
    rexlimdvaa
    mtod
    @6
    @10
    ioran
    sylanbrc
    vx
    cA
    dflim3
    sylanbrc
    cA
    cV
    r1limwun
    impbida
end
