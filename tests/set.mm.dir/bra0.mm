include "c0v.mm"
include "cbr.mm"
include "cfv.mm"
include "chil.mm"
include "cc0.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "wcel.mm"
include "wceq.mm"
include "ax-hv0cl.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "brafval.mm"
include "hi02.mm"
include "mpteq2ia.mm"
include "syl6eq.mm"
include "ax-mp.mm"
include "fconstmpt.mm"
include "eqtr4i.mm"

theorem bra0
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T


  assert |- ( bra ` 0h ) = ( ~H X. { 0 } )

  proof
    c0v
    cbr
    cfv
    #
    vx
    chil
    cc0
    cmpt
    #
    chil
    cc0
    csn
    cxp
    c0v
    chil
    wcel
    #
    @0
    @1
    wceq
    ax-hv0cl
    @2
    @0
    vx
    chil
    vx
    cv
    #
    c0v
    csp
    co
    #
    cmpt
    @1
    vx
    c0v
    brafval
    vx
    chil
    @4
    cc0
    @3
    hi02
    mpteq2ia
    syl6eq
    ax-mp
    vx
    chil
    cc0
    fconstmpt
    eqtr4i
end
