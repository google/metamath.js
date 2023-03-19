include "csp.mm"
include "cdip.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "cmv.mm"
include "cmin.mm"
include "ci.mm"
include "csm.mm"
include "cmul.mm"
include "caddc.mm"
include "c4.mm"
include "cdiv.mm"
include "polid.mm"
include "cnv.mm"
include "hhnv.mm"
include "hhba.mm"
include "hhva.mm"
include "hhsm.mm"
include "hhnm.mm"
include "eqid.mm"
include "hhvs.mm"
include "ipval3.mm"
include "mp3an1.mm"
include "eqtr4d.mm"
include "rgen2a.mm"
include "cxp.mm"
include "cc.mm"
include "wf.mm"
include "wb.mm"
include "ax-hfi.mm"
include "ipf.mm"
include "ax-mp.mm"
include "wfn.mm"
include "ffn.mm"
include "eqfnov2.mm"
include "syl2an.mm"
include "mp2an.mm"
include "mpbir.mm"

theorem hhip
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.


  assert |- .ih = ( .iOLD ` U )

  proof
    csp
    cU
    cdip
    cfv
    #
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    csp
    co
    #
    @2
    @3
    @0
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
    @6
    vx
    vy
    chil
    @2
    chil
    wcel
    #
    @3
    chil
    wcel
    #
    wa
    @4
    @2
    @3
    cva
    co
    cno
    cfv
    c2
    cexp
    co
    @2
    @3
    cmv
    co
    cno
    cfv
    c2
    cexp
    co
    cmin
    co
    ci
    @2
    ci
    @3
    csm
    co
    #
    cva
    co
    cno
    cfv
    c2
    cexp
    co
    @2
    @10
    cmv
    co
    cno
    cfv
    c2
    cexp
    co
    cmin
    co
    cmul
    co
    caddc
    co
    c4
    cdiv
    co
    #
    @5
    @2
    @3
    polid
    cU
    cnv
    wcel
    #
    @8
    @9
    @5
    @11
    wceq
    cU
    hhnv.1
    hhnv
    #
    @2
    @3
    @0
    csm
    cU
    cva
    cmv
    cno
    chil
    cU
    hhnv.1
    hhba
    #
    cU
    hhnv.1
    hhva
    cU
    hhnv.1
    hhsm
    cU
    hhnv.1
    hhnm
    @0
    eqid
    #
    cU
    hhnv.1
    hhvs
    ipval3
    mp3an1
    eqtr4d
    rgen2a
    chil
    chil
    cxp
    #
    cc
    csp
    wf
    #
    @16
    cc
    @0
    wf
    #
    @1
    @7
    wb
    #
    ax-hfi
    @12
    @18
    @13
    @0
    cU
    chil
    @14
    @15
    ipf
    ax-mp
    @17
    csp
    @16
    wfn
    @0
    @16
    wfn
    @19
    @18
    @16
    cc
    csp
    ffn
    @16
    cc
    @0
    ffn
    vx
    vy
    chil
    chil
    csp
    @0
    eqfnov2
    syl2an
    mp2an
    mpbir
end
