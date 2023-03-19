include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "com.mm"
include "cdif.mm"
include "wrex.mm"
include "wn.mm"
include "cfin7.mm"
include "wceq.mm"
include "breq1.mm"
include "rexbidv.mm"
include "notbid.mm"
include "df-fin7.mm"
include "elab2g.mm"

theorem isfin7
  let vy: setvar y
  let cA: class A
  let cV: class V
  let vx: setvar x
  let cB: class B
  let cX: class X

  disjoint A y
  disjoint x y
  disjoint A x
  disjoint B y
  disjoint X x
  assert |- ( A e. V -> ( A e. Fin7 <-> -. E. y e. ( On \ _om ) A ~~ y ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cen
    wbr
    #
    vy
    con0
    com
    cdif
    #
    wrex
    #
    wn
    cA
    @1
    cen
    wbr
    #
    vy
    @3
    wrex
    #
    wn
    vx
    cA
    cfin7
    cV
    @0
    cA
    wceq
    #
    @4
    @6
    @7
    @2
    @5
    vy
    @3
    @0
    cA
    @1
    cen
    breq1
    rexbidv
    notbid
    vx
    vy
    df-fin7
    elab2g
end
