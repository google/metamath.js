include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cline2.mm"
include "co.mm"
include "cv.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "cab.mm"
include "cin.mm"
include "crab.mm"
include "fvline.mm"
include "wss.mm"
include "wceq.mm"
include "liness.mm"
include "eqsstr3d.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqtr4d.mm"
include "dfrab2.mm"
include "syl6eqr.mm"

theorem fvline2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cN: class N

  disjoint N x
  disjoint A x
  disjoint B x
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ A =/= B ) ) -> ( A Line B ) = { x e. ( EE ` N ) | x Colinear <. A , B >. } )

  proof
    cN
    cn
    wcel
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @0
    wcel
    cA
    cB
    wne
    w3a
    wa
    #
    cA
    cB
    cline2
    co
    #
    vx
    cv
    cA
    cB
    cop
    ccolin
    wbr
    #
    vx
    cab
    #
    @0
    cin
    #
    @3
    vx
    @0
    crab
    @1
    @2
    @4
    @5
    vx
    cA
    cB
    cN
    fvline
    #
    @1
    @4
    @0
    wss
    @5
    @4
    wceq
    @1
    @4
    @2
    @0
    @6
    cA
    cB
    cN
    liness
    eqsstr3d
    @4
    @0
    df-ss
    sylib
    eqtr4d
    @3
    vx
    @0
    dfrab2
    syl6eqr
end
