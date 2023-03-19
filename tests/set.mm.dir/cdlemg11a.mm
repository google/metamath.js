include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "co.mm"
include "wne.mm"
include "w3a.mm"
include "simp33.mm"
include "wceq.mm"
include "simpr.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl31.mm"
include "simpl32.mm"
include "cdlemg6.mm"
include "syl113anc.mm"
include "oveq12d.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem cdlemg11a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemg8.l: |- .<_ = ( le ` K )
  assume cdlemg8.j: |- .\/ = ( join ` K )
  assume cdlemg8.m: |- ./\ = ( meet ` K )
  assume cdlemg8.a: |- A = ( Atoms ` K )
  assume cdlemg8.h: |- H = ( LHyp ` K )
  assume cdlemg8.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( F ` ( G ` P ) ) =/= P )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    wa
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    cP
    cG
    cfv
    cF
    cfv
    #
    cQ
    cG
    cfv
    cF
    cfv
    #
    c.or
    co
    #
    cP
    cQ
    c.or
    co
    #
    wne
    #
    w3a
    #
    w3a
    #
    @8
    @4
    cP
    wne
    @0
    @1
    @2
    @3
    @8
    simp33
    @10
    @4
    cP
    @6
    @7
    @10
    @4
    cP
    wceq
    #
    @6
    @7
    wceq
    @10
    @11
    wa
    #
    @4
    cP
    @5
    cQ
    c.or
    @10
    @11
    simpr
    #
    @12
    @0
    @1
    @2
    @3
    @11
    @5
    cQ
    wceq
    @0
    @1
    @9
    @11
    simpl1
    @0
    @1
    @9
    @11
    simpl2
    @2
    @3
    @8
    @0
    @1
    @11
    simpl31
    @2
    @3
    @8
    @0
    @1
    @11
    simpl32
    @13
    cA
    cP
    cQ
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    cdlemg6
    syl113anc
    oveq12d
    ex
    necon3d
    mpd
end
