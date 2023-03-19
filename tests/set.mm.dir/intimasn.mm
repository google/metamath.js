include "wcel.mm"
include "wal.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "cint.mm"
include "cima.mm"
include "wceq.mm"
include "cab.mm"
include "ax-5.mm"
include "r19.12sn.mm"
include "biimprd.mm"
include "alimi.mm"
include "intimag.mm"
include "3syl.mm"

theorem intimasn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let va: setvar a
  let vy: setvar y
  let vb: setvar b

  disjoint A a
  disjoint B a
  disjoint a x
  disjoint A x
  disjoint B x
  disjoint V y
  disjoint a b
  disjoint a y
  disjoint b y
  disjoint A b
  disjoint A y
  disjoint B b
  disjoint B y
  disjoint x y
  disjoint b x
  assert |- ( B e. V -> ( |^| A " { B } ) = |^| { x | E. a e. A x = ( a " { B } ) } )

  proof
    cB
    cV
    wcel
    #
    @0
    vy
    wal
    vb
    cv
    vy
    cv
    cop
    va
    cv
    #
    wcel
    #
    vb
    cB
    csn
    #
    wrex
    va
    cA
    wral
    #
    @2
    va
    cA
    wral
    vb
    @3
    wrex
    #
    wi
    #
    vy
    wal
    cA
    cint
    @3
    cima
    vx
    cv
    @1
    @3
    cima
    wceq
    va
    cA
    wrex
    vx
    cab
    cint
    wceq
    @0
    vy
    ax-5
    @0
    @6
    vy
    @0
    @5
    @4
    @2
    vb
    va
    cB
    cA
    cV
    r19.12sn
    biimprd
    alimi
    vx
    vy
    cA
    @3
    va
    vb
    intimag
    3syl
end
