include "cle.mm"
include "cvv.mm"
include "wcel.mm"
include "cxrs.mm"
include "cple.mm"
include "cfv.mm"
include "wceq.mm"
include "cxr.mm"
include "cxp.mm"
include "xrex.mm"
include "xpex.mm"
include "lerelxr.mm"
include "ssexi.mm"
include "cv.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "cxmu.mm"
include "cordt.mm"
include "df-xrs.mm"
include "odrngle.mm"
include "ax-mp.mm"

theorem xrsle
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- <_ = ( le ` RR*s )

  proof
    cle
    cvv
    wcel
    cle
    cxrs
    cple
    cfv
    wceq
    cle
    cxr
    cxr
    cxp
    cxr
    cxr
    xrex
    xrex
    xpex
    lerelxr
    ssexi
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
    odrngle
    ax-mp
end
