include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "cint.mm"
include "cima.mm"
include "wceq.mm"
include "cab.mm"
include "wb.mm"
include "r19.12.mm"
include "id.mm"
include "impbid2.mm"
include "elimaint.mm"
include "elintima.mm"
include "3bitr4g.mm"
include "alimi.mm"
include "dfcleq.mm"
include "sylibr.mm"

theorem intimag
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b

  disjoint a x
  disjoint a y
  disjoint A a
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B x
  disjoint B y
  disjoint A b
  disjoint B b
  disjoint a b
  disjoint b y
  disjoint b x
  assert |- ( A. y ( A. a e. A E. b e. B <. b , y >. e. a -> E. b e. B A. a e. A <. b , y >. e. a ) -> ( |^| A " B ) = |^| { x | E. a e. A x = ( a " B ) } )

  proof
    vb
    cv
    vy
    cv
    #
    cop
    va
    cv
    #
    wcel
    #
    vb
    cB
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
    cB
    wrex
    #
    wi
    #
    vy
    wal
    @0
    cA
    cint
    cB
    cima
    #
    wcel
    #
    @0
    vx
    cv
    @1
    cB
    cima
    wceq
    va
    cA
    wrex
    vx
    cab
    cint
    #
    wcel
    #
    wb
    #
    vy
    wal
    @6
    @8
    wceq
    @5
    @10
    vy
    @5
    @4
    @3
    @7
    @9
    @5
    @4
    @3
    @2
    vb
    va
    cB
    cA
    r19.12
    @5
    id
    impbid2
    vy
    cA
    cB
    va
    vb
    elimaint
    vx
    vy
    cA
    cB
    va
    vb
    elintima
    3bitr4g
    alimi
    vy
    @6
    @8
    dfcleq
    sylibr
end
