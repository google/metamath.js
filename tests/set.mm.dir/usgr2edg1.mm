include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "wne.mm"
include "cpr.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "wreu.mm"
include "wn.mm"
include "usgrumgr.mm"
include "umgr2edg1.mm"
include "sylanl1.mm"

theorem usgr2edg1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cE: class E
  let cG: class G
  let cI: class I
  let cN: class N
  let vy: setvar y
  assume usgrf1oedg.i: |- I = ( iEdg ` G )
  assume usgrf1oedg.e: |- E = ( Edg ` G )

  disjoint G x
  disjoint A x
  disjoint B x
  disjoint I x
  disjoint N x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint G y
  disjoint I y
  disjoint N y
  assert |- ( ( ( G e. USGraph /\ A =/= B ) /\ ( { N , A } e. E /\ { B , N } e. E ) ) -> -. E! x e. dom I N e. ( I ` x ) )

  proof
    cG
    cusgr
    wcel
    cG
    cumgr
    wcel
    cA
    cB
    wne
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
    cN
    vx
    cv
    cI
    cfv
    wcel
    vx
    cI
    cdm
    wreu
    wn
    cG
    usgrumgr
    vx
    cA
    cB
    cE
    cG
    cI
    cN
    usgrf1oedg.i
    usgrf1oedg.e
    umgr2edg1
    sylanl1
end
