include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "wceq.mm"
include "wrex.mm"
include "renegcl.mm"
include "recn.mm"
include "negnegd.mm"
include "eqcomd.mm"
include "negeq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem infm3lem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint A w
  disjoint u v
  disjoint t v
  disjoint A v
  disjoint t u
  disjoint A u
  disjoint A t
  assert |- ( x e. RR -> E. y e. RR x = -u y )

  proof
    vx
    cv
    #
    cr
    wcel
    #
    @0
    cneg
    #
    cr
    wcel
    @0
    @2
    cneg
    #
    wceq
    #
    @0
    vy
    cv
    #
    cneg
    #
    wceq
    #
    vy
    cr
    wrex
    @0
    renegcl
    @1
    @3
    @0
    @1
    @0
    @0
    recn
    negnegd
    eqcomd
    @7
    @4
    vy
    @2
    cr
    @5
    @2
    wceq
    @6
    @3
    @0
    @5
    @2
    negeq
    eqeq2d
    rspcev
    syl2anc
end
