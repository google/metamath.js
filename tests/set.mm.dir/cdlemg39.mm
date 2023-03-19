include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpl31.mm"
include "simpl32.mm"
include "simpr.mm"
include "cdlemg15.mm"
include "syl321anc.mm"
include "simpll1.mm"
include "simpll2.mm"
include "adantr.mm"
include "cdlemg14f.mm"
include "syl113anc.mm"
include "cdlemg14g.mm"
include "simpll3.mm"
include "simplr.mm"
include "cdlemg38.mm"
include "syl312anc.mm"
include "pm2.61da2ne.mm"
include "pm2.61dane.mm"

theorem cdlemg39
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vv: setvar v
  let vr: setvar r
  assume cdlemg35.l: |- .<_ = ( le ` K )
  assume cdlemg35.j: |- .\/ = ( join ` K )
  assume cdlemg35.m: |- ./\ = ( meet ` K )
  assume cdlemg35.a: |- A = ( Atoms ` K )
  assume cdlemg35.h: |- H = ( LHyp ` K )
  assume cdlemg35.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg35.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
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
    cQ
    wne
    #
    w3a
    #
    w3a
    #
    cP
    cP
    cG
    cfv
    #
    cF
    cfv
    c.or
    co
    cW
    c.an
    co
    cQ
    cQ
    cG
    cfv
    cF
    cfv
    c.or
    co
    cW
    c.an
    co
    wceq
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    @8
    @11
    @12
    wceq
    #
    wa
    @0
    @1
    @2
    @4
    @5
    @13
    @10
    @0
    @3
    @7
    @13
    simpl1
    @1
    @2
    @0
    @7
    @13
    simpl2l
    @1
    @2
    @0
    @7
    @13
    simpl2r
    @4
    @5
    @6
    @0
    @3
    @13
    simpl31
    @4
    @5
    @6
    @0
    @3
    @13
    simpl32
    @8
    @13
    simpr
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg35.l
    cdlemg35.j
    cdlemg35.m
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    cdlemg15
    syl321anc
    @8
    @11
    @12
    wne
    #
    wa
    #
    @10
    cP
    cF
    cfv
    #
    cP
    @9
    cP
    @15
    @16
    cP
    wceq
    #
    wa
    @0
    @3
    @4
    @5
    @17
    @10
    @0
    @3
    @7
    @14
    @17
    simpll1
    @0
    @3
    @7
    @14
    @17
    simpll2
    @15
    @4
    @17
    @4
    @5
    @6
    @0
    @3
    @14
    simpl31
    #
    adantr
    @15
    @5
    @17
    @4
    @5
    @6
    @0
    @3
    @14
    simpl32
    #
    adantr
    @15
    @17
    simpr
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg35.l
    cdlemg35.j
    cdlemg35.m
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    cdlemg14f
    syl113anc
    @15
    @9
    cP
    wceq
    #
    wa
    @0
    @3
    @4
    @5
    @20
    @10
    @0
    @3
    @7
    @14
    @20
    simpll1
    @0
    @3
    @7
    @14
    @20
    simpll2
    @15
    @4
    @20
    @18
    adantr
    @15
    @5
    @20
    @19
    adantr
    @15
    @20
    simpr
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg35.l
    cdlemg35.j
    cdlemg35.m
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    cdlemg14g
    syl113anc
    @15
    @16
    cP
    wne
    @9
    cP
    wne
    wa
    #
    wa
    @0
    @1
    @2
    @7
    @21
    @14
    @10
    @0
    @3
    @7
    @14
    @21
    simpll1
    @15
    @1
    @21
    @1
    @2
    @0
    @7
    @14
    simpl2l
    adantr
    @15
    @2
    @21
    @1
    @2
    @0
    @7
    @14
    simpl2r
    adantr
    @0
    @3
    @7
    @14
    @21
    simpll3
    @15
    @21
    simpr
    @8
    @14
    @21
    simplr
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg35.l
    cdlemg35.j
    cdlemg35.m
    cdlemg35.a
    cdlemg35.h
    cdlemg35.t
    cdlemg35.r
    cdlemg38
    syl312anc
    pm2.61da2ne
    pm2.61dane
end
