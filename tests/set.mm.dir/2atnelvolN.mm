include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "hlatjidm.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "wn.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "3atnelvolN.mm"
include "syl13anc.mm"
include "eqneltrrd.mm"

theorem 2atnelvolN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let cV: class V
  assume 3atnelvol.j: |- .\/ = ( join ` K )
  assume 3atnelvol.a: |- A = ( Atoms ` K )
  assume 3atnelvol.v: |- V = ( LVols ` K )


  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> -. ( P .\/ Q ) e. V )

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
    w3a
    #
    cP
    cP
    c.or
    co
    #
    cQ
    c.or
    co
    #
    cP
    cQ
    c.or
    co
    cV
    @3
    @4
    cP
    cQ
    c.or
    @0
    @1
    @4
    cP
    wceq
    @2
    cA
    c.or
    cK
    cP
    3atnelvol.j
    3atnelvol.a
    hlatjidm
    3adant3
    oveq1d
    @3
    @0
    @1
    @1
    @2
    @5
    cV
    wcel
    wn
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    #
    @6
    @0
    @1
    @2
    simp3
    cA
    cP
    cP
    cQ
    c.or
    cK
    cV
    3atnelvol.j
    3atnelvol.a
    3atnelvol.v
    3atnelvolN
    syl13anc
    eqneltrrd
end
