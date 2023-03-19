include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wrex.mm"
include "ps-2.mm"
include "ex.mm"

theorem paddasslem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vs: setvar s
  let vr: setvar r
  let vp: setvar p
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )

  disjoint A s
  disjoint .\/ s
  disjoint K s
  disjoint .<_ s
  disjoint p s
  disjoint r s
  disjoint s x
  disjoint s y
  disjoint s z
  assert |- ( ( K e. HL /\ ( x e. A /\ r e. A /\ y e. A ) /\ ( p e. A /\ z e. A ) ) -> ( ( ( -. x .<_ ( r .\/ y ) /\ p =/= z ) /\ ( p .<_ ( x .\/ r ) /\ z .<_ ( r .\/ y ) ) ) -> E. s e. A ( s .<_ ( x .\/ y ) /\ s .<_ ( p .\/ z ) ) ) )

  proof
    cK
    chlt
    wcel
    vx
    cv
    #
    cA
    wcel
    vr
    cv
    #
    cA
    wcel
    vy
    cv
    #
    cA
    wcel
    w3a
    vp
    cv
    #
    cA
    wcel
    vz
    cv
    #
    cA
    wcel
    wa
    w3a
    @0
    @1
    @2
    c.or
    co
    #
    c.le
    wbr
    wn
    @3
    @4
    wne
    wa
    @3
    @0
    @1
    c.or
    co
    c.le
    wbr
    @4
    @5
    c.le
    wbr
    wa
    wa
    vs
    cv
    #
    @0
    @2
    c.or
    co
    c.le
    wbr
    @6
    @3
    @4
    c.or
    co
    c.le
    wbr
    wa
    vs
    cA
    wrex
    vs
    cA
    @0
    @1
    @2
    @3
    @4
    c.or
    cK
    c.le
    paddasslem.l
    paddasslem.j
    paddasslem.a
    ps-2
    ex
end
