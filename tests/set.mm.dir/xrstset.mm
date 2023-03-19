include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "cxrs.mm"
include "cts.mm"
include "wceq.mm"
include "fvex.mm"
include "cxr.mm"
include "cv.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "cxmu.mm"
include "df-xrs.mm"
include "odrngtset.mm"
include "ax-mp.mm"

theorem xrstset
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- ( ordTop ` <_ ) = ( TopSet ` RR*s )

  proof
    cle
    cordt
    cfv
    #
    cvv
    wcel
    @0
    cxrs
    cts
    cfv
    wceq
    cle
    cordt
    fvex
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
    @2
    @1
    cxne
    cxad
    co
    @1
    @2
    cxne
    cxad
    co
    cif
    cmpt2
    cxad
    cxmu
    @0
    cle
    cvv
    cxrs
    vx
    vy
    df-xrs
    odrngtset
    ax-mp
end
