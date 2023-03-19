include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "wn.mm"
include "cal.mm"
include "cvlatl.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr3.mm"
include "atncmp.mm"
include "syl3anc.mm"
include "cbs.mm"
include "cfv.mm"
include "wi.mm"
include "eqid.mm"
include "atbase.mm"
include "cvlexchb1.mm"
include "3expia.mm"
include "syl3anr3.mm"
include "sylbird.mm"
include "3impia.mm"

theorem cvlatexchb1
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume cvlatexch.l: |- .<_ = ( le ` K )
  assume cvlatexch.j: |- .\/ = ( join ` K )
  assume cvlatexch.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ R e. A ) /\ P =/= R ) -> ( P .<_ ( R .\/ Q ) <-> ( R .\/ P ) = ( R .\/ Q ) ) )

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
    cR
    cA
    wcel
    #
    w3a
    #
    cP
    cR
    wne
    #
    cP
    cR
    cQ
    c.or
    co
    #
    c.le
    wbr
    cR
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
    cR
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
    cP
    cR
    cK
    c.le
    cvlatexch.l
    cvlatexch.a
    atncmp
    syl3anc
    @3
    @1
    @0
    @2
    cR
    cK
    cbs
    cfv
    #
    wcel
    #
    @9
    @7
    wi
    cA
    @11
    cR
    cK
    @11
    eqid
    #
    cvlatexch.a
    atbase
    @0
    @1
    @2
    @12
    w3a
    @9
    @7
    cA
    @11
    cP
    cQ
    c.or
    cK
    c.le
    cR
    @13
    cvlatexch.l
    cvlatexch.j
    cvlatexch.a
    cvlexchb1
    3expia
    syl3anr3
    sylbird
    3impia
end
