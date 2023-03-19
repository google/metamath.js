include "cxrs.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cxr.mm"
include "cop.mm"
include "cplusg.mm"
include "cxad.mm"
include "cmulr.mm"
include "cxmu.mm"
include "ctp.mm"
include "cts.mm"
include "cle.mm"
include "cordt.mm"
include "cple.mm"
include "cds.mm"
include "cv.mm"
include "wbr.mm"
include "cxne.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "cun.mm"
include "cvv.mm"
include "df-xrs.mm"
include "tpex.mm"
include "unex.mm"
include "eqeltri.mm"

theorem xrsex
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- RR*s e. _V

  proof
    cxrs
    cnx
    cbs
    cfv
    cxr
    cop
    #
    cnx
    cplusg
    cfv
    cxad
    cop
    #
    cnx
    cmulr
    cfv
    cxmu
    cop
    #
    ctp
    #
    cnx
    cts
    cfv
    cle
    cordt
    cfv
    cop
    #
    cnx
    cple
    cfv
    cle
    cop
    #
    cnx
    cds
    cfv
    vx
    vy
    cxr
    cxr
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    @7
    @6
    cxne
    cxad
    co
    @6
    @7
    cxne
    cxad
    co
    cif
    cmpt2
    cop
    #
    ctp
    #
    cun
    cvv
    vx
    vy
    df-xrs
    @3
    @9
    @0
    @1
    @2
    tpex
    @4
    @5
    @8
    tpex
    unex
    eqeltri
end
