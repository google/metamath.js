include "wss.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cqs.mm"
include "ssrexv.mm"
include "ss2abdv.mm"
include "df-qs.mm"
include "3sstr4g.mm"

theorem qsss1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( A C_ B -> ( A /. C ) C_ ( B /. C ) )

  proof
    cA
    cB
    wss
    #
    vy
    cv
    vx
    cv
    cC
    cec
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    @1
    vx
    cB
    wrex
    #
    vy
    cab
    cA
    cC
    cqs
    cB
    cC
    cqs
    @0
    @2
    @3
    vy
    @1
    vx
    cA
    cB
    ssrexv
    ss2abdv
    vx
    vy
    cA
    cC
    df-qs
    vx
    vy
    cB
    cC
    df-qs
    3sstr4g
end
