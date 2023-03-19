include "cusgr.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cpr.mm"
include "cumgr.mm"
include "cv.mm"
include "cfv.mm"
include "w3a.mm"
include "cdm.mm"
include "wrex.mm"
include "usgrumgr.mm"
include "anim1i.mm"
include "umgr2edg.mm"
include "syl.mm"

theorem usgr2edg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cE: class E
  let cG: class G
  let cI: class I
  let cN: class N
  assume usgrf1oedg.i: |- I = ( iEdg ` G )
  assume usgrf1oedg.e: |- E = ( Edg ` G )

  disjoint G x
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint N x
  disjoint N y
  assert |- ( ( ( G e. USGraph /\ A =/= B ) /\ ( { N , A } e. E /\ { B , N } e. E ) ) -> E. x e. dom I E. y e. dom I ( x =/= y /\ N e. ( I ` x ) /\ N e. ( I ` y ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cA
    cB
    wne
    #
    wa
    #
    cN
    cA
    cpr
    cE
    wcel
    cB
    cN
    cpr
    cE
    wcel
    wa
    #
    wa
    cG
    cumgr
    wcel
    #
    @1
    wa
    #
    @3
    wa
    vx
    cv
    #
    vy
    cv
    #
    wne
    cN
    @6
    cI
    cfv
    wcel
    cN
    @7
    cI
    cfv
    wcel
    w3a
    vy
    cI
    cdm
    #
    wrex
    vx
    @8
    wrex
    @2
    @5
    @3
    @0
    @4
    @1
    cG
    usgrumgr
    anim1i
    anim1i
    vx
    vy
    cA
    cB
    cE
    cG
    cI
    cN
    usgrf1oedg.i
    usgrf1oedg.e
    umgr2edg
    syl
end
