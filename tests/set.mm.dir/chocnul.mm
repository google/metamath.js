include "c0.mm"
include "cort.mm"
include "cfv.mm"
include "chil.mm"
include "cv.mm"
include "wcel.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "ral0.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "0ss.mm"
include "ocel.mm"
include "ax-mp.mm"
include "mpbiran2.mm"
include "eqriv.mm"

theorem chocnul
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( _|_ ` (/) ) = ~H

  proof
    vx
    c0
    cort
    cfv
    #
    chil
    vx
    cv
    #
    @0
    wcel
    #
    @1
    chil
    wcel
    #
    @1
    vy
    cv
    csp
    co
    cc0
    wceq
    #
    vy
    c0
    wral
    #
    @4
    vy
    ral0
    c0
    chil
    wss
    @2
    @3
    @5
    wa
    wb
    chil
    0ss
    vy
    @1
    c0
    ocel
    ax-mp
    mpbiran2
    eqriv
end
