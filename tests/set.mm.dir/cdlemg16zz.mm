include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "id.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "adantl.mm"
include "wne.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl31.mm"
include "simpr.mm"
include "simpl32.mm"
include "simpl33.mm"
include "cdlemg16z.mm"
include "syl332anc.mm"
include "pm2.61dane.mm"

theorem cdlemg16zz
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
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ -. ( R ` F ) .<_ ( P .\/ Q ) /\ -. ( R ` G ) .<_ ( P .\/ Q ) ) ) -> ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ W ) = ( ( Q .\/ ( F ` ( G ` Q ) ) ) ./\ W ) )

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
    cF
    cT
    wcel
    #
    w3a
    #
    cG
    cT
    wcel
    #
    cF
    cR
    cfv
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cG
    cR
    cfv
    @6
    c.le
    wbr
    wn
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
    #
    c.or
    co
    #
    cW
    c.an
    co
    cQ
    cQ
    cG
    cfv
    #
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    wceq
    #
    cP
    cQ
    cP
    cQ
    wceq
    #
    @17
    @10
    @18
    @13
    @16
    cW
    c.an
    @18
    cP
    cQ
    @12
    @15
    c.or
    @18
    id
    @18
    @11
    @14
    cF
    cP
    cQ
    cG
    fveq2
    fveq2d
    oveq12d
    oveq1d
    adantl
    @10
    cP
    cQ
    wne
    #
    wa
    @0
    @1
    @2
    @3
    @5
    @19
    @7
    @8
    @17
    @0
    @4
    @9
    @19
    simpl1
    @1
    @2
    @3
    @0
    @9
    @19
    simpl21
    @1
    @2
    @3
    @0
    @9
    @19
    simpl22
    @1
    @2
    @3
    @0
    @9
    @19
    simpl23
    @5
    @7
    @8
    @0
    @4
    @19
    simpl31
    @10
    @19
    simpr
    @5
    @7
    @8
    @0
    @4
    @19
    simpl32
    @5
    @7
    @8
    @0
    @4
    @19
    simpl33
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
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg16z
    syl332anc
    pm2.61dane
end
