include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "hlatj32.mm"
include "wceq.mm"
include "hlatjcom.mm"
include "3adant3r2.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem hlatjrot
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  assume hlatjcom.j: |- .\/ = ( join ` K )
  assume hlatjcom.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) ) -> ( ( P .\/ Q ) .\/ R ) = ( ( R .\/ P ) .\/ Q ) )

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
    wa
    #
    cP
    cQ
    c.or
    co
    cR
    c.or
    co
    cP
    cR
    c.or
    co
    #
    cQ
    c.or
    co
    cR
    cP
    c.or
    co
    #
    cQ
    c.or
    co
    cA
    cP
    cQ
    cR
    c.or
    cK
    hlatjcom.j
    hlatjcom.a
    hlatj32
    @4
    @5
    @6
    cQ
    c.or
    @0
    @1
    @3
    @5
    @6
    wceq
    @2
    cA
    c.or
    cK
    cP
    cR
    hlatjcom.j
    hlatjcom.a
    hlatjcom
    3adant3r2
    oveq1d
    eqtrd
end
