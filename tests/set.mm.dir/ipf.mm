include "cnv.mm"
include "wcel.mm"
include "cxp.mm"
include "cc.mm"
include "wf.mm"
include "c1.mm"
include "c4.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cns.mm"
include "cfv.mm"
include "cpv.mm"
include "cnmcv.mm"
include "c2.mm"
include "cmul.mm"
include "csu.mm"
include "cdiv.mm"
include "cmpt2.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "ipval.mm"
include "dipcl.mm"
include "eqeltrrd.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "fmpt2.mm"
include "sylib.mm"
include "dipfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem ipf
  let cP: class P
  let cU: class U
  let cX: class X
  let cA: class A
  let vk: setvar k
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  assume ipcl.1: |- X = ( BaseSet ` U )
  assume ipcl.7: |- P = ( .iOLD ` U )


  assert |- ( U e. NrmCVec -> P : ( X X. X ) --> CC )

  proof
    cU
    cnv
    wcel
    #
    cX
    cX
    cxp
    #
    cc
    cP
    wf
    @1
    cc
    vx
    vy
    cX
    cX
    c1
    c4
    cfz
    co
    ci
    vk
    cv
    cexp
    co
    #
    vx
    cv
    #
    @2
    vy
    cv
    #
    cU
    cns
    cfv
    #
    co
    cU
    cpv
    cfv
    #
    co
    cU
    cnmcv
    cfv
    #
    cfv
    c2
    cexp
    co
    cmul
    co
    vk
    csu
    c4
    cdiv
    co
    #
    cmpt2
    #
    wf
    #
    @0
    @8
    cc
    wcel
    #
    vy
    cX
    wral
    vx
    cX
    wral
    @10
    @0
    @11
    vx
    vy
    cX
    cX
    @0
    @3
    cX
    wcel
    #
    @4
    cX
    wcel
    #
    @11
    @0
    @12
    @13
    w3a
    @3
    @4
    cP
    co
    @8
    cc
    @3
    @4
    cP
    @5
    cU
    vk
    @6
    @7
    cX
    ipcl.1
    @6
    eqid
    #
    @5
    eqid
    #
    @7
    eqid
    #
    ipcl.7
    ipval
    @3
    @4
    cP
    cU
    cX
    ipcl.1
    ipcl.7
    dipcl
    eqeltrrd
    3expib
    ralrimivv
    vx
    vy
    cX
    cX
    @8
    cc
    @9
    @9
    eqid
    fmpt2
    sylib
    @0
    @1
    cc
    cP
    @9
    vx
    vy
    cP
    @5
    cU
    vk
    @6
    @7
    cX
    ipcl.1
    @14
    @15
    @16
    ipcl.7
    dipfval
    feq1d
    mpbird
end
