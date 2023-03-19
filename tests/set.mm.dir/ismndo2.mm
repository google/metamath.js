include "wcel.mm"
include "cdm.mm"
include "wceq.mm"
include "cmndo.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "w3a.mm"
include "wi.mm"
include "crn.mm"
include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "mndomgmid.mm"
include "rngopidOLD.mm"
include "syl.mm"
include "syl5eq.mm"
include "a1i.mm"
include "fdm.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6req.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "eqid.mm"
include "ismndo1.mm"
include "xpid11.mm"
include "biimpri.mm"
include "feq23.mm"
include "mpancom.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "rexeqbi1dv.mm"
include "3anbi123d.mm"
include "bibi2d.mm"
include "syl5ibrcom.mm"
include "pm5.21ndd.mm"

theorem ismndo2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cG: class G
  let cX: class X
  assume ismndo2.1: |- X = ran G

  disjoint G x
  disjoint G y
  disjoint G z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( G e. A -> ( G e. MndOp <-> ( G : ( X X. X ) --> X /\ A. x e. X A. y e. X A. z e. X ( ( x G y ) G z ) = ( x G ( y G z ) ) /\ E. x e. X A. y e. X ( ( x G y ) = y /\ ( y G x ) = y ) ) ) )

  proof
    cG
    cA
    wcel
    #
    cX
    cG
    cdm
    #
    cdm
    #
    wceq
    #
    cG
    cmndo
    wcel
    #
    cX
    cX
    cxp
    #
    cX
    cG
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    vz
    cv
    #
    cG
    co
    @7
    @8
    @10
    cG
    co
    cG
    co
    wceq
    #
    vz
    cX
    wral
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    @9
    @8
    wceq
    @8
    @7
    cG
    co
    @8
    wceq
    wa
    #
    vy
    cX
    wral
    #
    vx
    cX
    wrex
    #
    w3a
    #
    @4
    @3
    wi
    @0
    @4
    cX
    cG
    crn
    #
    @2
    ismndo2.1
    @4
    cG
    cmagm
    cexid
    cin
    wcel
    @19
    @2
    wceq
    cG
    mndomgmid
    cG
    rngopidOLD
    syl
    syl5eq
    a1i
    @18
    @3
    wi
    @0
    @6
    @14
    @3
    @17
    @6
    @2
    @5
    cdm
    cX
    @6
    @1
    @5
    @5
    cX
    cG
    fdm
    dmeqd
    cX
    dmxpid
    syl6req
    3ad2ant1
    a1i
    @0
    @4
    @18
    wb
    @3
    @4
    @2
    @2
    cxp
    #
    @2
    cG
    wf
    #
    @11
    vz
    @2
    wral
    #
    vy
    @2
    wral
    #
    vx
    @2
    wral
    #
    @15
    vy
    @2
    wral
    #
    vx
    @2
    wrex
    #
    w3a
    #
    wb
    vx
    vy
    vz
    cA
    cG
    @2
    @2
    eqid
    ismndo1
    @3
    @18
    @27
    @4
    @3
    @6
    @21
    @14
    @24
    @17
    @26
    @5
    @20
    wceq
    #
    @3
    @6
    @21
    wb
    @28
    @3
    cX
    @2
    xpid11
    biimpri
    @5
    cX
    @20
    @2
    cG
    feq23
    mpancom
    @13
    @23
    vx
    cX
    @2
    @12
    @22
    vy
    cX
    @2
    @11
    vz
    cX
    @2
    raleq
    raleqbi1dv
    raleqbi1dv
    @16
    @25
    vx
    cX
    @2
    @15
    vy
    cX
    @2
    raleq
    rexeqbi1dv
    3anbi123d
    bibi2d
    syl5ibrcom
    pm5.21ndd
end
