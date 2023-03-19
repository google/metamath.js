include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wtr.mm"
include "wcel.mm"
include "wss.mm"
include "wi.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "triun.mm"
include "r1tr.mm"
include "a1i.mm"
include "mprg.mm"
include "wceq.mm"
include "wb.mm"
include "wfun.mm"
include "cdm.mm"
include "wlim.mm"
include "r1funlim.mm"
include "simpli.mm"
include "funiunfv.mm"
include "ax-mp.mm"
include "treq.mm"
include "mpbi.mm"
include "trss.mm"

theorem r1elssi
  let cA: class A
  let vx: setvar x


  assert |- ( A e. U. ( R1 " On ) -> A C_ U. ( R1 " On ) )

  proof
    cr1
    con0
    cima
    cuni
    #
    wtr
    #
    cA
    @0
    wcel
    cA
    @0
    wss
    wi
    vx
    con0
    vx
    cv
    #
    cr1
    cfv
    #
    ciun
    #
    wtr
    #
    @1
    @3
    wtr
    #
    @5
    vx
    con0
    vx
    con0
    @3
    triun
    @6
    @2
    con0
    wcel
    @2
    r1tr
    a1i
    mprg
    @4
    @0
    wceq
    #
    @5
    @1
    wb
    cr1
    wfun
    #
    @7
    @8
    cr1
    cdm
    wlim
    r1funlim
    simpli
    vx
    con0
    cr1
    funiunfv
    ax-mp
    @4
    @0
    treq
    ax-mp
    mpbi
    @0
    cA
    trss
    ax-mp
end
