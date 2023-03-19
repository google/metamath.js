include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "eqid.mm"
include "cvlsupr2.mm"
include "simp2.mm"
include "syl6bi.mm"
include "3exp.mm"
include "imp4a.mm"
include "3imp.mm"

theorem cvlsupr6
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  assume cvlsupr5.a: |- A = ( Atoms ` K )
  assume cvlsupr5.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= Q /\ ( P .\/ R ) = ( Q .\/ R ) ) ) -> R =/= Q )

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
    cQ
    wne
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
    @4
    cR
    cP
    cQ
    c.or
    co
    cK
    cple
    cfv
    #
    wbr
    #
    w3a
    @4
    cA
    cP
    cQ
    cR
    c.or
    cK
    @6
    cvlsupr5.a
    @6
    eqid
    cvlsupr5.j
    cvlsupr2
    @5
    @4
    @7
    simp2
    syl6bi
    3exp
    imp4a
    3imp
end
