include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wa.mm"
include "ne0i.mm"
include "wi.mm"
include "ax-1.mm"
include "wn.mm"
include "wceq.mm"
include "cmpt.mm"
include "mpt2ndm0.mm"
include "fveq1.mm"
include "0fv.mm"
include "syl6eq.mm"
include "eqneqall.mm"
include "3syl.mm"
include "pm2.61i.mm"
include "syl.mm"

theorem elovmpt3imp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cM: class M
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume elovmpt3imp.o: |- O = ( x e. _V , y e. _V |-> ( z e. M |-> B ) )

  disjoint x y
  assert |- ( A e. ( ( X O Y ) ` Z ) -> ( X e. _V /\ Y e. _V ) )

  proof
    cA
    cZ
    cX
    cY
    cO
    co
    #
    cfv
    #
    wcel
    @1
    c0
    wne
    #
    cX
    cvv
    wcel
    cY
    cvv
    wcel
    wa
    #
    @1
    cA
    ne0i
    @3
    @2
    @3
    wi
    #
    @3
    @2
    ax-1
    @3
    wn
    @0
    c0
    wceq
    #
    @1
    c0
    wceq
    @4
    vx
    vy
    vz
    cM
    cB
    cmpt
    cO
    cX
    cY
    cvv
    cvv
    elovmpt3imp.o
    mpt2ndm0
    @5
    @1
    cZ
    c0
    cfv
    c0
    cZ
    @0
    c0
    fveq1
    cZ
    0fv
    syl6eq
    @3
    @1
    c0
    eqneqall
    3syl
    pm2.61i
    syl
end
