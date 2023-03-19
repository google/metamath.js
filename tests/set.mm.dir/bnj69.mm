include "w-bnj15.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "biid.mm"
include "bnj1189.mm"

theorem bnj69
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  assert |- ( ( R _FrSe A /\ B C_ A /\ B =/= (/) ) -> E. x e. B A. y e. B -. y R x )

  proof
    cA
    cR
    w-bnj15
    cB
    cA
    wss
    cB
    c0
    wne
    w3a
    #
    vx
    cv
    #
    cB
    wcel
    vy
    cv
    #
    cB
    wcel
    @2
    @1
    cR
    wbr
    #
    w3a
    #
    @3
    wn
    vy
    cB
    wral
    #
    vx
    vy
    cA
    cB
    cR
    @0
    biid
    @4
    biid
    @5
    biid
    bnj1189
end
