include "con0.mm"
include "wcel.mm"
include "cr1.mm"
include "cfv.mm"
include "cv.mm"
include "cpw.mm"
include "ciun.mm"
include "crnk.mm"
include "cab.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "r1val1.mm"
include "sylbir.mm"
include "wa.mm"
include "onelon.mm"
include "r1val2.mm"
include "syl.mm"
include "pweqd.mm"
include "iuneq2dv.mm"
include "eqtrd.mm"

theorem r1val3
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A e. On -> ( R1 ` A ) = U_ x e. A ~P { y | ( rank ` y ) e. x } )

  proof
    cA
    con0
    wcel
    #
    cA
    cr1
    cfv
    #
    vx
    cA
    vx
    cv
    #
    cr1
    cfv
    #
    cpw
    #
    ciun
    #
    vx
    cA
    vy
    cv
    crnk
    cfv
    @2
    wcel
    vy
    cab
    #
    cpw
    #
    ciun
    @0
    cA
    cr1
    cdm
    #
    wcel
    @1
    @5
    wceq
    @8
    con0
    cA
    cr1
    con0
    wfn
    @8
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    eleq2i
    vx
    cA
    r1val1
    sylbir
    @0
    vx
    cA
    @4
    @7
    @0
    @2
    cA
    wcel
    wa
    #
    @3
    @6
    @9
    @2
    con0
    wcel
    @3
    @6
    wceq
    cA
    @2
    onelon
    vy
    @2
    r1val2
    syl
    pweqd
    iuneq2dv
    eqtrd
end
