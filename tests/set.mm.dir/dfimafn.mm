include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wbr.mm"
include "cima.mm"
include "wcel.mm"
include "wb.mm"
include "ssel.mm"
include "funbrfvb.mm"
include "ex.mm"
include "syl9r.mm"
include "imp31.mm"
include "rexbidva.mm"
include "abbidv.mm"
include "dfima2.mm"
include "syl6reqr.mm"

theorem dfimafn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cB: class B
  let cY: class Y

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint B x
  disjoint B y
  disjoint Y x
  assert |- ( ( Fun F /\ A C_ dom F ) -> ( F " A ) = { y | E. x e. A ( F ` x ) = y } )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wss
    #
    wa
    #
    vx
    cv
    #
    cF
    cfv
    vy
    cv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    @4
    @5
    cF
    wbr
    #
    vx
    cA
    wrex
    #
    vy
    cab
    cF
    cA
    cima
    @3
    @7
    @9
    vy
    @3
    @6
    @8
    vx
    cA
    @0
    @2
    @4
    cA
    wcel
    #
    @6
    @8
    wb
    #
    @2
    @10
    @4
    @1
    wcel
    #
    @0
    @11
    cA
    @1
    @4
    ssel
    @0
    @12
    @11
    @4
    @5
    cF
    funbrfvb
    ex
    syl9r
    imp31
    rexbidva
    abbidv
    vx
    vy
    cF
    cA
    dfima2
    syl6reqr
end
