include "co.mm"
include "wceq.mm"
include "wne.mm"
include "wi.mm"
include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "df-ne.mm"
include "imbi1i.mm"
include "oveq1.mm"
include "biantrur.mm"
include "pm4.83.mm"
include "3bitrri.mm"
include "wb.mm"
include "cvlsupr2.mm"
include "3expia.mm"
include "pm5.74d.mm"
include "syl5bb.mm"

theorem cvlsupr3
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


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ R e. A ) ) -> ( ( P .\/ R ) = ( Q .\/ R ) <-> ( P =/= Q -> ( R =/= P /\ R =/= Q /\ R .<_ ( P .\/ Q ) ) ) ) )

  proof
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
    cP
    cQ
    wne
    #
    @0
    wi
    #
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
    wa
    #
    @1
    cR
    cP
    wne
    cR
    cQ
    wne
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    w3a
    #
    wi
    @2
    cP
    cQ
    wceq
    #
    wn
    #
    @0
    wi
    #
    @7
    @0
    wi
    #
    @9
    wa
    @0
    @1
    @8
    @0
    cP
    cQ
    df-ne
    imbi1i
    @10
    @9
    cP
    cQ
    cR
    c.or
    oveq1
    biantrur
    @7
    @0
    pm4.83
    3bitrri
    @5
    @1
    @0
    @6
    @3
    @4
    @1
    @0
    @6
    wb
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
    3expia
    pm5.74d
    syl5bb
end
