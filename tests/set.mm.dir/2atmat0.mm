include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "orcd.mm"
include "simpr3.mm"
include "2at0mat0.mm"
include "syl13anc.mm"

theorem 2atmat0
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let c.0: class .0.
  assume 2atmatz.j: |- .\/ = ( join ` K )
  assume 2atmatz.m: |- ./\ = ( meet ` K )
  assume 2atmatz.z: |- .0. = ( 0. ` K )
  assume 2atmatz.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A /\ ( P .\/ Q ) =/= ( R .\/ S ) ) ) -> ( ( ( P .\/ Q ) ./\ ( R .\/ S ) ) e. A \/ ( ( P .\/ Q ) ./\ ( R .\/ S ) ) = .0. ) )

  proof
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    w3a
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cP
    cQ
    c.or
    co
    #
    cR
    cS
    c.or
    co
    #
    wne
    #
    w3a
    #
    wa
    #
    @0
    @1
    @2
    cS
    c.0
    wceq
    #
    wo
    @5
    @3
    @4
    c.an
    co
    #
    cA
    wcel
    @9
    c.0
    wceq
    wo
    @0
    @6
    simpl
    @0
    @1
    @2
    @5
    simpr1
    @7
    @2
    @8
    @0
    @1
    @2
    @5
    simpr2
    orcd
    @0
    @1
    @2
    @5
    simpr3
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.an
    c.0
    2atmatz.j
    2atmatz.m
    2atmatz.z
    2atmatz.a
    2at0mat0
    syl13anc
end
