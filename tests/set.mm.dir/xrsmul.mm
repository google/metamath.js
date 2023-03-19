include "cxmu.mm"
include "cvv.mm"
include "wcel.mm"
include "cxrs.mm"
include "cmulr.mm"
include "cfv.mm"
include "wceq.mm"
include "cxr.mm"
include "cxp.mm"
include "wf.mm"
include "xmulf.mm"
include "xrex.mm"
include "xpex.mm"
include "fex2.mm"
include "mp3an.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "cordt.mm"
include "df-xrs.mm"
include "odrngmulr.mm"
include "ax-mp.mm"

theorem xrsmul
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- *e = ( .r ` RR*s )

  proof
    cxmu
    cvv
    wcel
    #
    cxmu
    cxrs
    cmulr
    cfv
    wceq
    cxr
    cxr
    cxp
    #
    cxr
    cxmu
    wf
    @1
    cvv
    wcel
    cxr
    cvv
    wcel
    @0
    xmulf
    cxr
    cxr
    xrex
    xrex
    xpex
    xrex
    @1
    cxr
    cxmu
    cvv
    cvv
    fex2
    mp3an
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
    @3
    @2
    cxne
    cxad
    co
    @2
    @3
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
    odrngmulr
    ax-mp
end
