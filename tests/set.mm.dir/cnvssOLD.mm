include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "ccnv.mm"
include "cop.mm"
include "wcel.mm"
include "ssel.mm"
include "df-br.mm"
include "3imtr4g.mm"
include "ssopab2dv.mm"
include "df-cnv.mm"
include "3sstr4g.mm"

theorem cnvssOLD
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
    @0
    @1
    @2
    cop
    #
    cA
    wcel
    @5
    cB
    wcel
    @3
    @4
    cA
    cB
    @5
    ssel
    @1
    @2
    cA
    df-br
    @1
    @2
    cB
    df-br
    3imtr4g
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
