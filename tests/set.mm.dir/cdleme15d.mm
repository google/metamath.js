include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "simp22l.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simp21l.mm"
include "wb.mm"
include "latmcl.mm"
include "syl5eqel.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"

theorem cdleme15d
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
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
  let cX: class X
  assume cdleme12.l: |- .<_ = ( le ` K )
  assume cdleme12.j: |- .\/ = ( join ` K )
  assume cdleme12.m: |- ./\ = ( meet ` K )
  assume cdleme12.a: |- A = ( Atoms ` K )
  assume cdleme12.h: |- H = ( LHyp ` K )
  assume cdleme12.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme12.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme12.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme15.c: |- C = ( ( P .\/ S ) ./\ W )
  assume cdleme15.x: |- X = ( ( P .\/ T ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ S =/= T ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ -. U .<_ ( S .\/ T ) ) ) -> ( X .\/ C ) .<_ W )

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
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cT
    cA
    wcel
    #
    cT
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cP
    cQ
    wne
    cS
    cT
    wne
    wa
    #
    w3a
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    cT
    @16
    c.le
    wbr
    wn
    cU
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    w3a
    #
    cX
    cW
    c.le
    wbr
    #
    cC
    cW
    c.le
    wbr
    #
    cX
    cC
    c.or
    co
    cW
    c.le
    wbr
    #
    @18
    cX
    cP
    cT
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme15.x
    @18
    cK
    clat
    wcel
    #
    @22
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @25
    wcel
    #
    @23
    cW
    c.le
    wbr
    @18
    @0
    @24
    @0
    @1
    @5
    @6
    @15
    @17
    simp11l
    #
    cK
    hllat
    syl
    #
    @18
    @0
    @3
    @11
    @26
    @28
    @3
    @4
    @2
    @6
    @15
    @17
    simp12l
    #
    @11
    @12
    @10
    @14
    @7
    @17
    simp22l
    cA
    @25
    c.or
    cK
    cP
    cT
    @25
    eqid
    #
    cdleme12.j
    cdleme12.a
    hlatjcl
    syl3anc
    #
    @18
    @1
    @27
    @0
    @1
    @5
    @6
    @15
    @17
    simp11r
    @25
    cH
    cK
    cW
    @31
    cdleme12.h
    lhpbase
    syl
    #
    @25
    cK
    c.le
    c.an
    @22
    cW
    @31
    cdleme12.l
    cdleme12.m
    latmle2
    syl3anc
    syl5eqbr
    @18
    cC
    cP
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme15.c
    @18
    @24
    @34
    @25
    wcel
    #
    @27
    @35
    cW
    c.le
    wbr
    @29
    @18
    @0
    @3
    @8
    @36
    @28
    @30
    @8
    @9
    @13
    @14
    @7
    @17
    simp21l
    cA
    @25
    c.or
    cK
    cP
    cS
    @31
    cdleme12.j
    cdleme12.a
    hlatjcl
    syl3anc
    #
    @33
    @25
    cK
    c.le
    c.an
    @34
    cW
    @31
    cdleme12.l
    cdleme12.m
    latmle2
    syl3anc
    syl5eqbr
    @18
    @24
    cX
    @25
    wcel
    cC
    @25
    wcel
    @27
    @19
    @20
    wa
    @21
    wb
    @29
    @18
    cX
    @23
    @25
    cdleme15.x
    @18
    @24
    @26
    @27
    @23
    @25
    wcel
    @29
    @32
    @33
    @25
    cK
    c.an
    @22
    cW
    @31
    cdleme12.m
    latmcl
    syl3anc
    syl5eqel
    @18
    cC
    @35
    @25
    cdleme15.c
    @18
    @24
    @36
    @27
    @35
    @25
    wcel
    @29
    @37
    @33
    @25
    cK
    c.an
    @34
    cW
    @31
    cdleme12.m
    latmcl
    syl3anc
    syl5eqel
    @33
    @25
    c.or
    cK
    c.le
    cX
    cC
    cW
    @31
    cdleme12.l
    cdleme12.j
    latjle12
    syl13anc
    mpbi2and
end
