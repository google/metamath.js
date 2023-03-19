include "clo.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "cc.mm"
include "cmap.mm"
include "crab.mm"
include "df-lnop.mm"
include "cnv.mm"
include "wcel.mm"
include "hhnv.mm"
include "hhba.mm"
include "hhva.mm"
include "hhsm.mm"
include "lnoval.mm"
include "mp2an.mm"
include "eqtr4i.mm"

theorem hhlnoi
  let cU: class U
  let cL: class L
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hhlno.1: |- U = <. <. +h , .h >. , normh >.
  assume hhlno.2: |- L = ( U LnOp U )


  assert |- LinOp = L

  proof
    clo
    vx
    cv
    #
    vy
    cv
    #
    csm
    co
    vz
    cv
    #
    cva
    co
    vt
    cv
    #
    cfv
    @0
    @1
    @3
    cfv
    csm
    co
    @2
    @3
    cfv
    cva
    co
    wceq
    vz
    chil
    wral
    vy
    chil
    wral
    vx
    cc
    wral
    vt
    chil
    chil
    cmap
    co
    crab
    #
    cL
    vx
    vy
    vz
    vt
    df-lnop
    cU
    cnv
    wcel
    #
    @5
    cL
    @4
    wceq
    cU
    hhlno.1
    hhnv
    #
    @6
    vx
    vy
    vz
    vt
    csm
    csm
    cU
    cva
    cva
    cL
    cU
    chil
    chil
    cU
    hhlno.1
    hhba
    #
    @7
    cU
    hhlno.1
    hhva
    #
    @8
    cU
    hhlno.1
    hhsm
    #
    @9
    hhlno.2
    lnoval
    mp2an
    eqtr4i
end
