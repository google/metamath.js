include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wbr.mm"
include "wi.mm"
include "cvlsupr2.mm"
include "simp3.mm"
include "syl6bi.mm"
include "3exp.mm"
include "imp4a.mm"
include "3imp.mm"

theorem cvlsupr4
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume cvlsupr2.a: |- A = ( Atoms ` K )
  assume cvlsupr2.l: |- .<_ = ( le ` K )
  assume cvlsupr2.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ ( P .\/ R ) = ( Q .\/ R ) ) ) -> R .<_ ( P .\/ Q ) )

  proof
    cK
    clc
    wcel
    #
    cP
    cA
    wcel
    cQ
    cA
    wcel
    cR
    cA
    wcel
    w3a
    #
    cP
    cQ
    wne
    #
    cP
    cR
    c.or
    co
    cQ
    cR
    c.or
    co
    wceq
    #
    wa
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    @0
    @1
    @2
    @3
    @4
    @0
    @1
    @2
    @3
    @4
    wi
    @0
    @1
    @2
    w3a
    @3
    cR
    cP
    wne
    #
    cR
    cQ
    wne
    #
    @4
    w3a
    @4
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    cvlsupr2.a
    cvlsupr2.l
    cvlsupr2.j
    cvlsupr2
    @5
    @6
    @4
    simp3
    syl6bi
    3exp
    imp4a
    3imp
end
