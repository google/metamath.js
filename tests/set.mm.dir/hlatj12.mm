include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "hlatjcom.mm"
include "3adant3r3.mm"
include "oveq1d.mm"
include "hlatjass.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr1.mm"
include "simpr3.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"

theorem hlatj12
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  assume hlatjcom.j: |- .\/ = ( join ` K )
  assume hlatjcom.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) ) -> ( P .\/ ( Q .\/ R ) ) = ( Q .\/ ( P .\/ R ) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    wa
    #
    cP
    cQ
    c.or
    co
    #
    cR
    c.or
    co
    cQ
    cP
    c.or
    co
    #
    cR
    c.or
    co
    #
    cP
    cQ
    cR
    c.or
    co
    c.or
    co
    cQ
    cP
    cR
    c.or
    co
    c.or
    co
    #
    @5
    @6
    @7
    cR
    c.or
    @0
    @1
    @2
    @6
    @7
    wceq
    @3
    cA
    c.or
    cK
    cP
    cQ
    hlatjcom.j
    hlatjcom.a
    hlatjcom
    3adant3r3
    oveq1d
    cA
    cP
    cQ
    cR
    c.or
    cK
    hlatjcom.j
    hlatjcom.a
    hlatjass
    @5
    @0
    @2
    @1
    @3
    @8
    @9
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr3
    cA
    cQ
    cP
    cR
    c.or
    cK
    hlatjcom.j
    hlatjcom.a
    hlatjass
    syl13anc
    3eqtr3d
end
