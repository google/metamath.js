include "cfi.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "ctb.mm"
include "fvex.mm"
include "fiin.mm"
include "rgen2a.mm"
include "fiinbas.mm"
include "mp2an.mm"

theorem fibas
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cB: class B
  let cJ: class J
  let cV: class V
  let cC: class C


  assert |- ( fi ` A ) e. TopBases

  proof
    cA
    cfi
    cfv
    #
    cvv
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cin
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    @0
    wral
    @0
    ctb
    wcel
    cA
    cfi
    fvex
    @3
    vx
    vy
    @0
    @1
    @2
    cA
    fiin
    rgen2a
    vx
    vy
    @0
    cvv
    fiinbas
    mp2an
end
