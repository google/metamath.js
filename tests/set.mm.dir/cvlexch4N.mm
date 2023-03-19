include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "wa.mm"
include "wn.mm"
include "cal.mm"
include "cvlatl.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr3.mm"
include "atnle.mm"
include "syl3anc.mm"
include "cvlexchb1.mm"
include "3expia.mm"
include "sylbird.mm"
include "3impia.mm"

theorem cvlexch4N
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let c.0: class .0.
  assume cvlexch3.b: |- B = ( Base ` K )
  assume cvlexch3.l: |- .<_ = ( le ` K )
  assume cvlexch3.j: |- .\/ = ( join ` K )
  assume cvlexch3.m: |- ./\ = ( meet ` K )
  assume cvlexch3.z: |- .0. = ( 0. ` K )
  assume cvlexch3.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ X e. B ) /\ ( P ./\ X ) = .0. ) -> ( P .<_ ( X .\/ Q ) <-> ( X .\/ P ) = ( X .\/ Q ) ) )

  proof
    cK
    clc
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
    cX
    cB
    wcel
    #
    w3a
    #
    cP
    cX
    c.an
    co
    c.0
    wceq
    #
    cP
    cX
    cQ
    c.or
    co
    #
    c.le
    wbr
    cX
    cP
    c.or
    co
    @6
    wceq
    wb
    #
    @0
    @4
    wa
    #
    @5
    cP
    cX
    c.le
    wbr
    wn
    #
    @7
    @8
    cK
    cal
    wcel
    #
    @1
    @3
    @9
    @5
    wb
    @0
    @10
    @4
    cK
    cvlatl
    adantr
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
    cB
    cP
    cK
    c.le
    c.an
    cX
    c.0
    cvlexch3.b
    cvlexch3.l
    cvlexch3.m
    cvlexch3.z
    cvlexch3.a
    atnle
    syl3anc
    @0
    @4
    @9
    @7
    cA
    cB
    cP
    cQ
    c.or
    cK
    c.le
    cX
    cvlexch3.b
    cvlexch3.l
    cvlexch3.j
    cvlexch3.a
    cvlexchb1
    3expia
    sylbird
    3impia
end
