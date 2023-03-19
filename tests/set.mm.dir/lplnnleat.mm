include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "eqid.mm"
include "lplnnle2at.mm"
include "syl13anc.mm"
include "wceq.mm"
include "hlatjidm.mm"
include "3adant2.mm"
include "breq2d.mm"
include "mtbid.mm"

theorem lplnnleat
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cK: class K
  let c.le: class .<_
  let cX: class X
  assume lplnnleat.l: |- .<_ = ( le ` K )
  assume lplnnleat.a: |- A = ( Atoms ` K )
  assume lplnnleat.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ X e. P /\ Q e. A ) -> -. X .<_ Q )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cX
    cQ
    cQ
    cK
    cjn
    cfv
    #
    co
    #
    c.le
    wbr
    #
    cX
    cQ
    c.le
    wbr
    @3
    @0
    @1
    @2
    @2
    @6
    wn
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    #
    @7
    cA
    cP
    cQ
    cQ
    @4
    cK
    c.le
    cX
    lplnnleat.l
    @4
    eqid
    #
    lplnnleat.a
    lplnnleat.p
    lplnnle2at
    syl13anc
    @3
    @5
    cQ
    cX
    c.le
    @0
    @2
    @5
    cQ
    wceq
    @1
    cA
    @4
    cK
    cQ
    @8
    lplnnleat.a
    hlatjidm
    3adant2
    breq2d
    mtbid
end
