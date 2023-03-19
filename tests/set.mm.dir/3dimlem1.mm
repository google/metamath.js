include "wceq.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "neeq1.mm"
include "oveq1.mm"
include "breq2d.mm"
include "notbid.mm"
include "oveq1d.mm"
include "3anbi123d.mm"
include "biimparc.mm"

theorem 3dimlem1
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  assume 3dim0.j: |- .\/ = ( join ` K )
  assume 3dim0.l: |- .<_ = ( le ` K )
  assume 3dim0.a: |- A = ( Atoms ` K )


  assert |- ( ( ( Q =/= R /\ -. S .<_ ( Q .\/ R ) /\ -. T .<_ ( ( Q .\/ R ) .\/ S ) ) /\ P = Q ) -> ( P =/= R /\ -. S .<_ ( P .\/ R ) /\ -. T .<_ ( ( P .\/ R ) .\/ S ) ) )

  proof
    cP
    cQ
    wceq
    #
    cP
    cR
    wne
    #
    cS
    cP
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cT
    @2
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    cQ
    cR
    wne
    #
    cS
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cT
    @9
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    @0
    @1
    @8
    @4
    @11
    @7
    @14
    cP
    cQ
    cR
    neeq1
    @0
    @3
    @10
    @0
    @2
    @9
    cS
    c.le
    cP
    cQ
    cR
    c.or
    oveq1
    #
    breq2d
    notbid
    @0
    @6
    @13
    @0
    @5
    @12
    cT
    c.le
    @0
    @2
    @9
    cS
    c.or
    @15
    oveq1d
    breq2d
    notbid
    3anbi123d
    biimparc
end
