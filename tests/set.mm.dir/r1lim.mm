include "wcel.mm"
include "wlim.mm"
include "cr1.mm"
include "cdm.mm"
include "cfv.mm"
include "cv.mm"
include "ciun.mm"
include "wceq.mm"
include "wa.mm"
include "con0.mm"
include "limelon.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "syl6eleqr.mm"
include "r1limg.mm"
include "sylancom.mm"

theorem r1lim
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( ( A e. B /\ Lim A ) -> ( R1 ` A ) = U_ x e. A ( R1 ` x ) )

  proof
    cA
    cB
    wcel
    #
    cA
    wlim
    #
    cA
    cr1
    cdm
    #
    wcel
    cA
    cr1
    cfv
    vx
    cA
    vx
    cv
    cr1
    cfv
    ciun
    wceq
    @0
    @1
    wa
    cA
    con0
    @2
    cA
    cB
    limelon
    cr1
    con0
    wfn
    @2
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    syl6eleqr
    vx
    cA
    r1limg
    sylancom
end
