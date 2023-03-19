include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "simp11.mm"
include "simp22.mm"
include "simp1.mm"
include "simp21.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "simp11l.mm"
include "simp22l.mm"
include "simpld.mm"
include "hlatlej2.mm"
include "simp23.mm"
include "oveq2d.mm"
include "trljat1.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "simp31.mm"
include "simp32.mm"
include "simp33.mm"
include "necomd.mm"
include "eqid.mm"
include "cdlemh.mm"
include "syl133anc.mm"
include "ltrniotacl.mm"

theorem cdlemki
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )
  assume cdlemk.i: |- I = ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` G ) ) ./\ ( ( N ` P ) .\/ ( R ` ( G o. `' F ) ) ) ) )

  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ i
  disjoint A i
  disjoint F i
  disjoint H i
  disjoint K i
  disjoint N i
  disjoint P i
  disjoint R i
  disjoint T i
  disjoint W i
  disjoint G i
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ ( R ` G ) =/= ( R ` F ) ) ) -> I e. T )

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
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
    #
    cN
    cT
    wcel
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
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    #
    wceq
    #
    w3a
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cG
    @14
    wne
    #
    cG
    cR
    cfv
    #
    @10
    wne
    #
    w3a
    #
    w3a
    #
    @2
    @9
    cP
    @17
    c.or
    co
    cP
    cN
    cfv
    #
    cG
    cF
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    #
    cA
    wcel
    @22
    cW
    c.le
    wbr
    wn
    wa
    #
    cI
    cT
    wcel
    @2
    @3
    @4
    @13
    @19
    simp11
    #
    @5
    @6
    @9
    @12
    @19
    simp22
    #
    @20
    @5
    @9
    @21
    cA
    wcel
    #
    @21
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @21
    cP
    @10
    c.or
    co
    #
    c.le
    wbr
    @15
    @16
    @10
    @17
    wne
    @23
    @5
    @13
    @19
    simp1
    @25
    @20
    @2
    @6
    @9
    @28
    @24
    @5
    @6
    @9
    @12
    @19
    simp21
    #
    @25
    cA
    cP
    cT
    cN
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnel
    #
    syl3anc
    @20
    @21
    cP
    @21
    c.or
    co
    #
    @29
    c.le
    @20
    @0
    @7
    @26
    @21
    @32
    c.le
    wbr
    @0
    @1
    @3
    @4
    @13
    @19
    simp11l
    @7
    @8
    @6
    @12
    @5
    @19
    simp22l
    @20
    @2
    @6
    @9
    @26
    @24
    @30
    @25
    @2
    @6
    @9
    w3a
    @26
    @27
    @31
    simpld
    syl3anc
    cA
    cP
    @21
    c.or
    cK
    c.le
    cdlemk.l
    cdlemk.j
    cdlemk.a
    hlatlej2
    syl3anc
    @20
    @29
    cP
    @11
    c.or
    co
    #
    @32
    @20
    @10
    @11
    cP
    c.or
    @5
    @6
    @9
    @12
    @19
    simp23
    oveq2d
    @20
    @2
    @6
    @9
    @33
    @32
    wceq
    @24
    @30
    @25
    cA
    cP
    cR
    cT
    cN
    cH
    c.or
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trljat1
    syl3anc
    eqtr2d
    breqtrd
    @5
    @13
    @15
    @16
    @18
    simp31
    @5
    @13
    @15
    @16
    @18
    simp32
    @20
    @17
    @10
    @5
    @13
    @15
    @16
    @18
    simp33
    necomd
    cA
    cB
    cP
    @21
    cR
    @22
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.m
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    @22
    eqid
    cdlemh
    syl133anc
    cA
    cP
    @22
    cT
    vi
    cI
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.i
    ltrniotacl
    syl3anc
end
