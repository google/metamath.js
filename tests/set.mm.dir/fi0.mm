include "c0.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "cint.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cab.mm"
include "cvv.mm"
include "wcel.mm"
include "0ex.mm"
include "fival.mm"
include "ax-mp.mm"
include "vprc.mm"
include "id.mm"
include "wss.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwi.mm"
include "ss0.mm"
include "3syl.mm"
include "inteqd.mm"
include "int0.mm"
include "syl6eq.mm"
include "sylan9eqr.mm"
include "rexlimiva.mm"
include "vex.mm"
include "syl6eqelr.mm"
include "mto.mm"
include "abf.mm"
include "eqtri.mm"

theorem fi0
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cV: class V


  assert |- ( fi ` (/) ) = (/)

  proof
    c0
    cfi
    cfv
    #
    vy
    cv
    #
    vx
    cv
    #
    cint
    #
    wceq
    #
    vx
    c0
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vy
    cab
    #
    c0
    c0
    cvv
    wcel
    @0
    @8
    wceq
    0ex
    vx
    vy
    c0
    cvv
    fival
    ax-mp
    @7
    vy
    @7
    cvv
    cvv
    wcel
    vprc
    @7
    cvv
    @1
    cvv
    @4
    @1
    cvv
    wceq
    vx
    @6
    @4
    @2
    @6
    wcel
    #
    @1
    @3
    cvv
    @4
    id
    @9
    @3
    c0
    cint
    cvv
    @9
    @2
    c0
    @9
    @2
    @5
    wcel
    @2
    c0
    wss
    @2
    c0
    wceq
    @6
    @5
    @2
    @5
    cfn
    inss1
    sseli
    @2
    c0
    elpwi
    @2
    ss0
    3syl
    inteqd
    int0
    syl6eq
    sylan9eqr
    rexlimiva
    vy
    vex
    syl6eqelr
    mto
    abf
    eqtri
end
