include "cbo.mm"
include "cv.mm"
include "cnop.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "clo.mm"
include "crab.mm"
include "df-bdop.mm"
include "cnv.mm"
include "wcel.mm"
include "wceq.mm"
include "hhnv.mm"
include "cnmoo.mm"
include "co.mm"
include "eqid.mm"
include "hhnmoi.mm"
include "clno.mm"
include "hhlnoi.mm"
include "bloval.mm"
include "mp2an.mm"
include "eqtr4i.mm"

theorem hhbloi
  let cB: class B
  let cU: class U
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  assume hhnmo.1: |- U = <. <. +h , .h >. , normh >.
  assume hhblo.2: |- B = ( U BLnOp U )


  assert |- BndLinOp = B

  proof
    cbo
    vx
    cv
    cnop
    cfv
    cpnf
    clt
    wbr
    vx
    clo
    crab
    #
    cB
    vx
    df-bdop
    cU
    cnv
    wcel
    #
    @1
    cB
    @0
    wceq
    cU
    hhnmo.1
    hhnv
    #
    @2
    vx
    cB
    cU
    clo
    cnop
    cU
    cU
    cU
    cU
    cnmoo
    co
    #
    hhnmo.1
    @3
    eqid
    hhnmoi
    cU
    cU
    cU
    clno
    co
    #
    hhnmo.1
    @4
    eqid
    hhlnoi
    hhblo.2
    bloval
    mp2an
    eqtr4i
end
