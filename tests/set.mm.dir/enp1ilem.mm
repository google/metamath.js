include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "cun.mm"
include "wcel.mm"
include "uneq1.mm"
include "undif1.mm"
include "uncom.mm"
include "eqtr4i.mm"
include "3eqtr3g.mm"
include "wss.mm"
include "snssi.mm"
include "ssequn2.mm"
include "sylib.mm"
include "eqeq1d.mm"
include "syl5ib.mm"

theorem enp1ilem
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cT: class T
  assume enp1ilem.1: |- T = ( { x } u. S )


  assert |- ( x e. A -> ( ( A \ { x } ) = S -> A = T ) )

  proof
    cA
    vx
    cv
    #
    csn
    #
    cdif
    #
    cS
    wceq
    #
    cA
    @1
    cun
    #
    cT
    wceq
    @0
    cA
    wcel
    #
    cA
    cT
    wceq
    @3
    @2
    @1
    cun
    cS
    @1
    cun
    #
    @4
    cT
    @2
    cS
    @1
    uneq1
    cA
    @1
    undif1
    @6
    @1
    cS
    cun
    cT
    cS
    @1
    uncom
    enp1ilem.1
    eqtr4i
    3eqtr3g
    @5
    @4
    cA
    cT
    @5
    @1
    cA
    wss
    @4
    cA
    wceq
    @0
    cA
    snssi
    @1
    cA
    ssequn2
    sylib
    eqeq1d
    syl5ib
end
