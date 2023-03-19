include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wcel.mm"
include "wrex.mm"
include "con0.mm"
include "wral.mm"
include "cvv.mm"
include "wn.mm"
include "wss.mm"
include "wb.mm"
include "rankon.mm"
include "ontri1.mm"
include "mpan.mm"
include "ralbidv.mm"
include "ralnex.mm"
include "syl6bb.mm"
include "rexbiia.mm"
include "rexnal.mm"
include "bitri.mm"
include "bndrank.mm"
include "sylbir.mm"
include "con1i.mm"

theorem unbndrank
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( -. A e. _V -> A. x e. On E. y e. A x e. ( rank ` y ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    crnk
    cfv
    #
    wcel
    #
    vy
    cA
    wrex
    #
    vx
    con0
    wral
    #
    cA
    cvv
    wcel
    #
    @5
    wn
    #
    @2
    @0
    wss
    #
    vy
    cA
    wral
    #
    vx
    con0
    wrex
    #
    @6
    @10
    @4
    wn
    #
    vx
    con0
    wrex
    @7
    @9
    @11
    vx
    con0
    @0
    con0
    wcel
    #
    @9
    @3
    wn
    #
    vy
    cA
    wral
    @11
    @12
    @8
    @13
    vy
    cA
    @2
    con0
    wcel
    @12
    @8
    @13
    wb
    @1
    rankon
    @2
    @0
    ontri1
    mpan
    ralbidv
    @3
    vy
    cA
    ralnex
    syl6bb
    rexbiia
    @4
    vx
    con0
    rexnal
    bitri
    vx
    vy
    cA
    bndrank
    sylbir
    con1i
end
