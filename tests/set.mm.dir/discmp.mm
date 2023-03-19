include "cfn.mm"
include "wcel.mm"
include "cpw.mm"
include "ccmp.mm"
include "ctop.mm"
include "cin.mm"
include "distop.mm"
include "pwfi.mm"
include "biimpi.mm"
include "elind.mm"
include "fincmp.mm"
include "syl.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "csn.mm"
include "cmpt.mm"
include "crn.mm"
include "wrex.mm"
include "wss.mm"
include "wf.mm"
include "wa.mm"
include "simpr.mm"
include "snssd.mm"
include "snex.mm"
include "elpw.mm"
include "sylibr.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "cab.mm"
include "ciun.mm"
include "rnmpt.mm"
include "unieqi.mm"
include "dfiun2.mm"
include "iunid.mm"
include "3eqtr2ri.mm"
include "a1i.mm"
include "unipw.mm"
include "eqcomi.mm"
include "cmpcov.mm"
include "mpd3an23.mm"
include "elin.mm"
include "simprbi.mm"
include "simplbi.mm"
include "elpwid.mm"
include "wral.mm"
include "snfi.mm"
include "rgenw.mm"
include "fmpt.mm"
include "mpbi.mm"
include "mp1i.mm"
include "sstrd.mm"
include "unifi.mm"
include "syl2anc.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "impbii.mm"

theorem discmp
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cJ: class J
  let cS: class S
  let cX: class X


  assert |- ( A e. Fin <-> ~P A e. Comp )

  proof
    cA
    cfn
    wcel
    #
    cA
    cpw
    #
    ccmp
    wcel
    #
    @0
    @1
    ctop
    cfn
    cin
    wcel
    @2
    @0
    ctop
    cfn
    @1
    cA
    cfn
    distop
    @0
    @1
    cfn
    wcel
    cA
    pwfi
    biimpi
    elind
    @1
    fincmp
    syl
    @2
    cA
    vy
    cv
    #
    cuni
    #
    wceq
    #
    vy
    vx
    cA
    vx
    cv
    #
    csn
    #
    cmpt
    #
    crn
    #
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @0
    @2
    @9
    @1
    wss
    #
    cA
    @9
    cuni
    #
    wceq
    #
    @12
    @2
    cA
    @1
    @8
    wf
    @13
    @2
    vx
    cA
    @7
    @1
    @8
    @2
    @6
    cA
    wcel
    #
    wa
    #
    @7
    cA
    wss
    @7
    @1
    wcel
    @17
    @6
    cA
    @2
    @16
    simpr
    snssd
    @7
    cA
    @6
    snex
    #
    elpw
    sylibr
    @8
    eqid
    #
    fmptd
    cA
    @1
    @8
    frn
    syl
    @15
    @2
    @14
    @3
    @7
    wceq
    vx
    cA
    wrex
    vy
    cab
    #
    cuni
    vx
    cA
    @7
    ciun
    cA
    @9
    @20
    vx
    vy
    cA
    @7
    @8
    @19
    rnmpt
    unieqi
    vx
    vy
    cA
    @7
    @18
    dfiun2
    vx
    cA
    iunid
    3eqtr2ri
    a1i
    @9
    @1
    cA
    vy
    @1
    cuni
    cA
    cA
    unipw
    eqcomi
    cmpcov
    mpd3an23
    @5
    @0
    vy
    @11
    @3
    @11
    wcel
    #
    @0
    @5
    @4
    cfn
    wcel
    #
    @21
    @3
    cfn
    wcel
    #
    @3
    cfn
    wss
    @22
    @21
    @3
    @10
    wcel
    #
    @23
    @3
    @10
    cfn
    elin
    #
    simprbi
    @21
    @3
    @9
    cfn
    @21
    @3
    @9
    @21
    @24
    @23
    @25
    simplbi
    elpwid
    cA
    cfn
    @8
    wf
    #
    @9
    cfn
    wss
    @21
    @7
    cfn
    wcel
    #
    vx
    cA
    wral
    @26
    @27
    vx
    cA
    @6
    snfi
    rgenw
    vx
    cA
    cfn
    @7
    @8
    @19
    fmpt
    mpbi
    cA
    cfn
    @8
    frn
    mp1i
    sstrd
    @3
    unifi
    syl2anc
    cA
    @4
    cfn
    eleq1
    syl5ibrcom
    rexlimiv
    syl
    impbii
end
