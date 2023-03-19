include "csslt.mm"
include "wbr.mm"
include "cv.mm"
include "csn.mm"
include "cbday.mm"
include "cfv.mm"
include "cun.mm"
include "cima.mm"
include "cuni.mm"
include "csuc.mm"
include "wss.mm"
include "w3a.mm"
include "csur.mm"
include "wrex.mm"
include "cscut.mm"
include "co.mm"
include "etasslt.mm"
include "wcel.mm"
include "wa.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "scutbday.mm"
include "adantr.mm"
include "wfn.mm"
include "bdayfn.mm"
include "ssrab2.mm"
include "simprl.mm"
include "simprr1.mm"
include "simprr2.mm"
include "jca.mm"
include "weq.mm"
include "sneq.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "fnfvima.mm"
include "mp3an12i.mm"
include "intss1.mm"
include "syl.mm"
include "eqsstrd.mm"
include "simprr3.mm"
include "sstrd.mm"
include "rexlimdvaa.mm"
include "mpd.mm"

theorem scutbdaybnd
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A <<s B -> ( bday ` ( A |s B ) ) C_ suc U. ( bday " ( A u. B ) ) )

  proof
    cA
    cB
    csslt
    wbr
    #
    cA
    vx
    cv
    #
    csn
    #
    csslt
    wbr
    #
    @2
    cB
    csslt
    wbr
    #
    @1
    cbday
    cfv
    #
    cbday
    cA
    cB
    cun
    cima
    cuni
    csuc
    #
    wss
    #
    w3a
    #
    vx
    csur
    wrex
    cA
    cB
    cscut
    co
    cbday
    cfv
    #
    @6
    wss
    #
    vx
    cA
    cB
    etasslt
    @0
    @8
    @10
    vx
    csur
    @0
    @1
    csur
    wcel
    #
    @8
    wa
    #
    wa
    #
    @9
    @5
    @6
    @13
    @9
    cbday
    cA
    vy
    cv
    #
    csn
    #
    csslt
    wbr
    #
    @15
    cB
    csslt
    wbr
    #
    wa
    #
    vy
    csur
    crab
    #
    cima
    #
    cint
    #
    @5
    @0
    @9
    @21
    wceq
    @12
    vy
    cA
    cB
    scutbday
    adantr
    @13
    @5
    @20
    wcel
    #
    @21
    @5
    wss
    cbday
    csur
    wfn
    @19
    csur
    wss
    @13
    @1
    @19
    wcel
    #
    @22
    bdayfn
    @18
    vy
    csur
    ssrab2
    @13
    @11
    @3
    @4
    wa
    #
    @23
    @0
    @11
    @8
    simprl
    @13
    @3
    @4
    @3
    @4
    @7
    @11
    @0
    simprr1
    @3
    @4
    @7
    @11
    @0
    simprr2
    jca
    @18
    @24
    vy
    @1
    csur
    vy
    vx
    weq
    #
    @16
    @3
    @17
    @4
    @25
    @15
    @2
    cA
    csslt
    @14
    @1
    sneq
    #
    breq2d
    @25
    @15
    @2
    cB
    csslt
    @26
    breq1d
    anbi12d
    elrab
    sylanbrc
    csur
    @19
    cbday
    @1
    fnfvima
    mp3an12i
    @5
    @20
    intss1
    syl
    eqsstrd
    @3
    @4
    @7
    @11
    @0
    simprr3
    sstrd
    rexlimdvaa
    mpd
end
