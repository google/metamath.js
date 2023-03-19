include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp21l.mm"
include "simp1.mm"
include "simp23.mm"
include "simp31.mm"
include "ltrncoat.mm"
include "syl121anc.mm"
include "simp1r.mm"
include "simp21.mm"
include "simp22l.mm"
include "simp32.mm"
include "cdleme0a.mm"
include "syl212anc.mm"
include "simp33.mm"
include "simp22.mm"
include "cdlemg2l.mm"
include "syl122anc.mm"
include "cdlemg3a.mm"
include "syl211anc.mm"
include "3netr3d.mm"
include "necomd.mm"
include "2llnma3r.mm"
include "syl131anc.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "hlatlej2.mm"
include "eqbrtrd.mm"

theorem cdlemg9a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
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
  assume cdlemg9.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ P =/= Q /\ ( ( F ` ( G ` P ) ) .\/ ( F ` ( G ` Q ) ) ) =/= ( P .\/ Q ) ) ) -> ( ( P .\/ U ) ./\ ( ( F ` ( G ` P ) ) .\/ U ) ) .<_ ( ( G ` P ) .\/ U ) )

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
    #
    cP
    cW
    c.le
    wbr
    wn
    #
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
    cU
    c.or
    co
    #
    @14
    cU
    c.or
    co
    #
    c.an
    co
    #
    cU
    @13
    cU
    c.or
    co
    #
    c.le
    @19
    @0
    @3
    @14
    cA
    wcel
    #
    cU
    cA
    wcel
    #
    @20
    @21
    wne
    @22
    cU
    wceq
    @0
    @1
    @10
    @18
    simp1l
    #
    @3
    @4
    @8
    @9
    @2
    @18
    simp21l
    #
    @19
    @2
    @9
    @11
    @3
    @24
    @2
    @10
    @18
    simp1
    #
    @2
    @5
    @8
    @9
    @18
    simp23
    #
    @2
    @10
    @11
    @12
    @17
    simp31
    #
    @27
    cA
    cP
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
    ltrncoat
    syl121anc
    @19
    @0
    @1
    @5
    @6
    @12
    @25
    @26
    @0
    @1
    @10
    @18
    simp1r
    #
    @2
    @5
    @8
    @9
    @18
    simp21
    #
    @6
    @7
    @5
    @9
    @2
    @18
    simp22l
    #
    @2
    @10
    @11
    @12
    @17
    simp32
    cA
    cP
    cQ
    cU
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
    cdlemg9.u
    cdleme0a
    syl212anc
    #
    @19
    @21
    @20
    @19
    @15
    @16
    @21
    @20
    @2
    @10
    @11
    @12
    @17
    simp33
    @19
    @2
    @5
    @8
    @9
    @11
    @15
    @21
    wceq
    @28
    @32
    @2
    @5
    @8
    @9
    @18
    simp22
    @29
    @30
    cA
    cP
    cQ
    cT
    cU
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
    cdlemg9.u
    cdlemg2l
    syl122anc
    @19
    @0
    @1
    @5
    @6
    @16
    @20
    wceq
    @26
    @31
    @32
    @33
    cA
    cP
    cQ
    cU
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
    cdlemg9.u
    cdlemg3a
    syl211anc
    3netr3d
    necomd
    cA
    cP
    @14
    cU
    c.or
    cK
    c.le
    c.an
    cdlemg8.l
    cdlemg8.j
    cdlemg8.m
    cdlemg8.a
    2llnma3r
    syl131anc
    @19
    @0
    @13
    cA
    wcel
    #
    @25
    cU
    @23
    c.le
    wbr
    @26
    @19
    @2
    @11
    @3
    @35
    @28
    @30
    @27
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg8.l
    cdlemg8.a
    cdlemg8.h
    cdlemg8.t
    ltrnat
    syl3anc
    @34
    cA
    @13
    cU
    c.or
    cK
    c.le
    cdlemg8.l
    cdlemg8.j
    cdlemg8.a
    hlatlej2
    syl3anc
    eqbrtrd
end
