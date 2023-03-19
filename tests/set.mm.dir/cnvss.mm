include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "ccnv.mm"
include "ssbr.mm"
include "ssopab2dv.mm"
include "df-cnv.mm"
include "3sstr4g.mm"

theorem cnvss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A C_ B -> `' A C_ `' B )

  proof
    cA
    cB
    wss
    #
    vy
    cv
    #
    vx
    cv
    #
    cA
    wbr
    #
    vx
    vy
    copab
    @1
    @2
    cB
    wbr
    #
    vx
    vy
    copab
    cA
    ccnv
    cB
    ccnv
    @0
    @3
    @4
    vx
    vy
    cA
    cB
    @1
    @2
    ssbr
    ssopab2dv
    vx
    vy
    cA
    df-cnv
    vx
    vy
    cB
    df-cnv
    3sstr4g
end
