include "cxr.mm"
include "cvv.mm"
include "wcel.mm"
include "cxrs.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "xrex.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "cxmu.mm"
include "cordt.mm"
include "df-xrs.mm"
include "odrngbas.mm"
include "ax-mp.mm"

theorem xrsbas
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- RR* = ( Base ` RR*s )

  proof
    cxr
    cvv
    wcel
    cxr
    cxrs
    cbs
    cfv
    wceq
    xrex
    cxr
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
    @1
    @0
    cxne
    cxad
    co
    @0
    @1
    cxne
    cxad
    co
    cif
    cmpt2
    cxad
    cxmu
    cle
    cordt
    cfv
    cle
    cvv
    cxrs
    vx
    vy
    df-xrs
    odrngbas
    ax-mp
end
