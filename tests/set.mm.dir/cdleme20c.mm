include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cp1.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp21l.mm"
include "simp22l.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "syl.mm"
include "hlatlej1.mm"
include "atmod2i1.mm"
include "syl131anc.mm"
include "simp21.mm"
include "lhpjat1.mm"
include "syl21anc.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "syl2anc.mm"
include "3eqtrrd.mm"
include "oveq1d.mm"
include "simp22r.mm"
include "simp3r.mm"
include "simp3l.mm"
include "cdlemeda.mm"
include "syl223anc.mm"
include "simp23.mm"
include "hlatjass.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "clat.mm"
include "hllat.mm"
include "latmle2.mm"
include "atmod1i1.mm"
include "eqtr4d.mm"
include "oveq12i.mm"
include "syl6reqr.mm"

theorem cdleme20c
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
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
  let cV: class V
  let cW: class W
  let cY: class Y
  assume cdleme19.l: |- .<_ = ( le ` K )
  assume cdleme19.j: |- .\/ = ( join ` K )
  assume cdleme19.m: |- ./\ = ( meet ` K )
  assume cdleme19.a: |- A = ( Atoms ` K )
  assume cdleme19.h: |- H = ( LHyp ` K )
  assume cdleme19.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme19.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme19.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme19.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme19.y: |- Y = ( ( R .\/ T ) ./\ W )
  assume cdleme20.v: |- V = ( ( S .\/ T ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ T e. A ) /\ ( -. S .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) ) -> ( D .\/ Y ) = ( ( ( R .\/ S ) .\/ T ) ./\ W ) )

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
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
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
    #
    cR
    @11
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cR
    cS
    c.or
    co
    #
    cT
    c.or
    co
    #
    cW
    c.an
    co
    #
    @16
    cW
    c.an
    co
    #
    cR
    cT
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    cD
    cY
    c.or
    co
    @15
    @18
    @19
    @20
    c.or
    co
    #
    cW
    c.an
    co
    #
    @22
    @15
    @17
    @23
    cW
    c.an
    @15
    @17
    @19
    cR
    c.or
    co
    #
    cT
    c.or
    co
    #
    @23
    @15
    @16
    @25
    cT
    c.or
    @15
    @25
    @16
    cW
    cR
    c.or
    co
    #
    c.an
    co
    #
    @16
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @16
    @15
    @0
    @3
    @16
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @31
    wcel
    #
    cR
    @16
    c.le
    wbr
    #
    @25
    @28
    wceq
    @0
    @1
    @10
    @14
    simp1l
    #
    @3
    @4
    @8
    @9
    @2
    @14
    simp21l
    #
    @15
    @0
    @3
    @6
    @32
    @35
    @36
    @6
    @7
    @5
    @9
    @2
    @14
    simp22l
    #
    cA
    @31
    c.or
    cK
    cR
    cS
    @31
    eqid
    #
    cdleme19.j
    cdleme19.a
    hlatjcl
    syl3anc
    #
    @15
    @1
    @33
    @0
    @1
    @10
    @14
    simp1r
    #
    @31
    cH
    cK
    cW
    @38
    cdleme19.h
    lhpbase
    syl
    #
    @15
    @0
    @3
    @6
    @34
    @35
    @36
    @37
    cA
    cR
    cS
    c.or
    cK
    c.le
    cdleme19.l
    cdleme19.j
    cdleme19.a
    hlatlej1
    syl3anc
    cA
    @31
    cR
    c.or
    cK
    c.le
    c.an
    @16
    cW
    @38
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    atmod2i1
    syl131anc
    @15
    @27
    @29
    @16
    c.an
    @15
    @0
    @1
    @5
    @27
    @29
    wceq
    @35
    @40
    @2
    @5
    @8
    @9
    @14
    simp21
    cA
    cR
    @29
    cH
    c.or
    cK
    c.le
    cW
    cdleme19.l
    cdleme19.j
    @29
    eqid
    #
    cdleme19.a
    cdleme19.h
    lhpjat1
    syl21anc
    oveq2d
    @15
    cK
    col
    wcel
    #
    @32
    @30
    @16
    wceq
    @15
    @0
    @43
    @35
    cK
    hlol
    syl
    @39
    @31
    @29
    cK
    c.an
    @16
    @38
    cdleme19.m
    @42
    olm11
    syl2anc
    3eqtrrd
    oveq1d
    @15
    @0
    @19
    cA
    wcel
    #
    @3
    @9
    @26
    @23
    wceq
    @35
    @15
    @0
    @1
    @6
    @7
    @3
    @13
    @12
    @44
    @35
    @40
    @37
    @6
    @7
    @5
    @9
    @2
    @14
    simp22r
    @36
    @2
    @10
    @12
    @13
    simp3r
    @2
    @10
    @12
    @13
    simp3l
    cA
    @19
    cP
    cQ
    cR
    cS
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    @19
    eqid
    cdlemeda
    syl223anc
    #
    @36
    @2
    @5
    @8
    @9
    @14
    simp23
    #
    cA
    @19
    cR
    cT
    c.or
    cK
    cdleme19.j
    cdleme19.a
    hlatjass
    syl13anc
    eqtrd
    oveq1d
    @15
    @0
    @44
    @20
    @31
    wcel
    #
    @33
    @19
    cW
    c.le
    wbr
    #
    @22
    @24
    wceq
    @35
    @45
    @15
    @0
    @3
    @9
    @47
    @35
    @36
    @46
    cA
    @31
    c.or
    cK
    cR
    cT
    @38
    cdleme19.j
    cdleme19.a
    hlatjcl
    syl3anc
    @41
    @15
    cK
    clat
    wcel
    #
    @32
    @33
    @48
    @15
    @0
    @49
    @35
    cK
    hllat
    syl
    @39
    @41
    @31
    cK
    c.le
    c.an
    @16
    cW
    @38
    cdleme19.l
    cdleme19.m
    latmle2
    syl3anc
    cA
    @31
    @19
    c.or
    cK
    c.le
    c.an
    @20
    cW
    @38
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    atmod1i1
    syl131anc
    eqtr4d
    cD
    @19
    cY
    @21
    c.or
    cdleme19.d
    cdleme19.y
    oveq12i
    syl6reqr
end
