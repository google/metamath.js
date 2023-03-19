include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "hlatexch2.mm"
include "con3dimp.mm"

theorem paddasslem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vr: setvar r
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ ( x e. A /\ r e. A /\ y e. A ) /\ x =/= y ) /\ -. r .<_ ( x .\/ y ) ) -> -. x .<_ ( r .\/ y ) )

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
    @0
    @2
    wne
    w3a
    @0
    @1
    @2
    c.or
    co
    c.le
    wbr
    @1
    @0
    @2
    c.or
    co
    c.le
    wbr
    cA
    @0
    @1
    @2
    c.or
    cK
    c.le
    paddasslem.l
    paddasslem.j
    paddasslem.a
    hlatexch2
    con3dimp
end
