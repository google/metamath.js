include "chlt.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "clln.mm"
include "cfv.mm"
include "wn.mm"
include "wa.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eqid.mm"
include "llni2.mm"
include "syl31anc.mm"
include "llnneat.mm"
include "syldan.mm"

theorem 2atneat
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  assume 2atneat.j: |- .\/ = ( join ` K )
  assume 2atneat.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ P =/= Q ) ) -> -. ( P .\/ Q ) e. A )

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
    cP
    cQ
    wne
    #
    w3a
    #
    cP
    cQ
    c.or
    co
    #
    cK
    clln
    cfv
    #
    wcel
    #
    @5
    cA
    wcel
    wn
    @0
    @4
    wa
    @0
    @1
    @2
    @3
    @7
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr3
    cA
    cP
    cQ
    c.or
    cK
    @6
    2atneat.j
    2atneat.a
    @6
    eqid
    #
    llni2
    syl31anc
    cA
    cK
    @6
    @5
    2atneat.a
    @8
    llnneat
    syldan
end
