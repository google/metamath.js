include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "cdlemg9a.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp21.mm"
include "simp22l.mm"
include "cdlemg3a.mm"
include "syl211anc.mm"
include "simp1.mm"
include "simp22.mm"
include "simp23.mm"
include "simp31.mm"
include "cdlemg2l.mm"
include "syl122anc.mm"
include "oveq12d.mm"
include "cdlemg2k.mm"
include "syl121anc.mm"
include "3brtr4d.mm"

theorem cdlemg9b
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ P =/= Q /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( ( P .\/ Q ) ./\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) ) .<_ ( ( G ` P ) .\/ ( G ` Q ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
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
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
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
    cP
    cQ
    wne
    #
    cP
    cG
    cfv
    #
    cF
    cfv
    #
    cQ
    cG
    cfv
    #
    cF
    cfv
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
    cP
    @15
    cW
    c.an
    co
    #
    c.or
    co
    #
    @12
    @19
    c.or
    co
    #
    c.an
    co
    @11
    @19
    c.or
    co
    #
    @15
    @14
    c.an
    co
    @11
    @13
    c.or
    co
    #
    c.le
    cA
    cP
    cQ
    cT
    @19
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg8.l
    cdlemg8.j
    cdlemg8.m
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    @19
    eqid
    #
    cdlemg9a
    @18
    @15
    @20
    @14
    @21
    c.an
    @18
    @0
    @1
    @3
    @4
    @15
    @20
    wceq
    @0
    @1
    @8
    @17
    simp1l
    @0
    @1
    @8
    @17
    simp1r
    @2
    @3
    @6
    @7
    @17
    simp21
    #
    @4
    @5
    @3
    @7
    @2
    @17
    simp22l
    cA
    cP
    cQ
    @19
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg8.l
    cdlemg8.j
    cdlemg8.m
    cdlemg8.a
    cdlemg8.h
    @24
    cdlemg3a
    syl211anc
    @18
    @2
    @3
    @6
    @7
    @9
    @14
    @21
    wceq
    @2
    @8
    @17
    simp1
    #
    @25
    @2
    @3
    @6
    @7
    @17
    simp22
    #
    @2
    @3
    @6
    @7
    @17
    simp23
    @2
    @8
    @9
    @10
    @16
    simp31
    #
    cA
    cP
    cQ
    cT
    @19
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg8.h
    cdlemg8.t
    cdlemg8.l
    cdlemg8.j
    cdlemg8.a
    cdlemg8.m
    @24
    cdlemg2l
    syl122anc
    oveq12d
    @18
    @2
    @3
    @6
    @9
    @23
    @22
    wceq
    @26
    @25
    @27
    @28
    cA
    cP
    cQ
    cT
    @19
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemg8.h
    cdlemg8.t
    cdlemg8.l
    cdlemg8.j
    cdlemg8.a
    cdlemg8.m
    @24
    cdlemg2k
    syl121anc
    3brtr4d
end
