include "cnop.mm"
include "chil.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "df-nmop.mm"
include "cnv.mm"
include "wcel.mm"
include "hhnv.mm"
include "hhba.mm"
include "hhnm.mm"
include "nmoofval.mm"
include "mp2an.mm"
include "eqtr4i.mm"

theorem hhnmoi
  let cU: class U
  let cN: class N
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  assume hhnmo.1: |- U = <. <. +h , .h >. , normh >.
  assume hhnmo.2: |- N = ( U normOpOLD U )


  assert |- normop = N

  proof
    cnop
    vt
    chil
    chil
    cmap
    co
    vy
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    vx
    cv
    @0
    vt
    cv
    cfv
    cno
    cfv
    wceq
    wa
    vy
    chil
    wrex
    vx
    cab
    cxr
    clt
    csup
    cmpt
    #
    cN
    vx
    vy
    vt
    df-nmop
    cU
    cnv
    wcel
    #
    @2
    cN
    @1
    wceq
    cU
    hhnmo.1
    hhnv
    #
    @3
    vx
    vy
    vt
    cU
    cno
    cno
    cN
    cU
    chil
    chil
    cU
    hhnmo.1
    hhba
    #
    @4
    cU
    hhnmo.1
    hhnm
    #
    @5
    hhnmo.2
    nmoofval
    mp2an
    eqtr4i
end
