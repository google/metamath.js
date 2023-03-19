include "cxad.mm"
include "cvv.mm"
include "wcel.mm"
include "cxrs.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "cxr.mm"
include "cxp.mm"
include "wf.mm"
include "xaddf.mm"
include "xrex.mm"
include "xpex.mm"
include "fex2.mm"
include "mp3an.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "cxmu.mm"
include "cordt.mm"
include "df-xrs.mm"
include "odrngplusg.mm"
include "ax-mp.mm"

theorem xrsadd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- +e = ( +g ` RR*s )

  proof
    cxad
    cvv
    wcel
    #
    cxad
    cxrs
    cplusg
    cfv
    wceq
    cxr
    cxr
    cxp
    #
    cxr
    cxad
    wf
    @1
    cvv
    wcel
    cxr
    cvv
    wcel
    @0
    xaddf
    cxr
    cxr
    xrex
    xrex
    xpex
    xrex
    @1
    cxr
    cxad
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
    odrngplusg
    ax-mp
end
