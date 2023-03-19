include "cv.mm"
include "ccom.mm"
include "cado.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cbo.mm"
include "wf.mm"
include "adjbdln.mm"
include "bdopf.mm"
include "mp2b.mm"
include "hocoi.mm"
include "oveq2d.mm"
include "adantl.mm"
include "ax-mp.mm"
include "oveq1d.mm"
include "adantr.mm"
include "ffvelrni.mm"
include "cdm.mm"
include "bdopadj.mm"
include "adj2.mm"
include "mp3an1.mm"
include "sylan.mm"
include "sylan2.mm"
include "3eqtrd.mm"
include "bdopcoi.mm"
include "3eqtr2rd.mm"
include "rgen2a.mm"
include "wb.mm"
include "hocofi.mm"
include "hoeq2.mm"
include "mp2an.mm"
include "mpbi.mm"

theorem adjcoi
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume nmoptri.1: |- S e. BndLinOp
  assume nmoptri.2: |- T e. BndLinOp


  assert |- ( adjh ` ( S o. T ) ) = ( ( adjh ` T ) o. ( adjh ` S ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cS
    cT
    ccom
    #
    cado
    cfv
    #
    cfv
    csp
    co
    #
    @0
    @1
    cT
    cado
    cfv
    #
    cS
    cado
    cfv
    #
    ccom
    #
    cfv
    #
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    @3
    @7
    wceq
    #
    @10
    vx
    vy
    chil
    @0
    chil
    wcel
    #
    @1
    chil
    wcel
    #
    wa
    #
    @9
    @0
    @1
    @6
    cfv
    #
    @5
    cfv
    #
    csp
    co
    #
    @0
    @2
    cfv
    #
    @1
    csp
    co
    #
    @4
    @14
    @9
    @18
    wceq
    @13
    @14
    @8
    @17
    @0
    csp
    @1
    @5
    @6
    cT
    cbo
    wcel
    #
    @5
    cbo
    wcel
    chil
    chil
    @5
    wf
    nmoptri.2
    cT
    adjbdln
    @5
    bdopf
    mp2b
    #
    cS
    cbo
    wcel
    #
    @6
    cbo
    wcel
    chil
    chil
    @6
    wf
    nmoptri.1
    cS
    adjbdln
    @6
    bdopf
    mp2b
    #
    hocoi
    oveq2d
    adantl
    @15
    @20
    @0
    cT
    cfv
    #
    cS
    cfv
    #
    @1
    csp
    co
    #
    @25
    @16
    csp
    co
    #
    @18
    @13
    @20
    @27
    wceq
    @14
    @13
    @19
    @26
    @1
    csp
    @0
    cS
    cT
    @23
    chil
    chil
    cS
    wf
    nmoptri.1
    cS
    bdopf
    ax-mp
    @21
    chil
    chil
    cT
    wf
    nmoptri.2
    cT
    bdopf
    ax-mp
    #
    hocoi
    oveq1d
    adantr
    @13
    @25
    chil
    wcel
    #
    @14
    @27
    @28
    wceq
    #
    chil
    chil
    @0
    cT
    @29
    ffvelrni
    cS
    cado
    cdm
    #
    wcel
    #
    @30
    @14
    @31
    @23
    @33
    nmoptri.1
    cS
    bdopadj
    ax-mp
    @25
    @1
    cS
    adj2
    mp3an1
    sylan
    @14
    @13
    @16
    chil
    wcel
    #
    @28
    @18
    wceq
    #
    chil
    chil
    @1
    @6
    @24
    ffvelrni
    cT
    @32
    wcel
    #
    @13
    @34
    @35
    @21
    @36
    nmoptri.2
    cT
    bdopadj
    ax-mp
    @0
    @16
    cT
    adj2
    mp3an1
    sylan2
    3eqtrd
    @2
    @32
    wcel
    #
    @13
    @14
    @20
    @4
    wceq
    @2
    cbo
    wcel
    #
    @37
    cS
    cT
    nmoptri.1
    nmoptri.2
    bdopcoi
    #
    @2
    bdopadj
    ax-mp
    @0
    @1
    @2
    adj2
    mp3an1
    3eqtr2rd
    rgen2a
    chil
    chil
    @3
    wf
    #
    chil
    chil
    @7
    wf
    @11
    @12
    wb
    @38
    @3
    cbo
    wcel
    @40
    @39
    @2
    adjbdln
    @3
    bdopf
    mp2b
    @5
    @6
    @22
    @24
    hocofi
    vx
    vy
    @3
    @7
    hoeq2
    mp2an
    mpbi
end
