include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "oveq1i.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp22.mm"
include "simp23.mm"
include "simp21.mm"
include "simp33.mm"
include "simp32.mm"
include "cdlemeda.mm"
include "syl223anc.mm"
include "simp31.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "atmod4i1.mm"
include "syl131anc.mm"
include "cdleme10.mm"
include "syl212anc.mm"
include "oveq1d.mm"
include "hlatj32.mm"
include "syl13anc.mm"
include "eqtr3d.mm"
include "eqtr4d.mm"
include "syl5eq.mm"

theorem cdleme20aN
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( R e. A /\ S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. S .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) ) -> ( V .\/ D ) = ( ( ( S .\/ R ) .\/ T ) ./\ W ) )

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
    w3a
    #
    cT
    cA
    wcel
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
    @8
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cV
    cD
    c.or
    co
    cS
    cT
    c.or
    co
    #
    cW
    c.an
    co
    #
    cD
    c.or
    co
    #
    cS
    cR
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
    cV
    @14
    cD
    c.or
    cdleme20.v
    oveq1i
    @12
    @15
    @13
    cD
    c.or
    co
    #
    cW
    c.an
    co
    #
    @18
    @12
    @0
    cD
    cA
    wcel
    #
    @13
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @22
    wcel
    #
    cD
    cW
    c.le
    wbr
    @15
    @20
    wceq
    @0
    @1
    @6
    @11
    simp1l
    #
    @12
    @0
    @1
    @4
    @5
    @3
    @10
    @9
    @21
    @25
    @0
    @1
    @6
    @11
    simp1r
    #
    @2
    @3
    @4
    @5
    @11
    simp22
    #
    @2
    @3
    @4
    @5
    @11
    simp23
    #
    @2
    @3
    @4
    @5
    @11
    simp21
    #
    @2
    @6
    @7
    @9
    @10
    simp33
    @2
    @6
    @7
    @9
    @10
    simp32
    cA
    cD
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
    cdleme19.d
    cdlemeda
    syl223anc
    #
    @12
    @0
    @4
    @7
    @23
    @25
    @27
    @2
    @6
    @7
    @9
    @10
    simp31
    #
    cA
    @22
    c.or
    cK
    cS
    cT
    @22
    eqid
    #
    cdleme19.j
    cdleme19.a
    hlatjcl
    syl3anc
    @12
    @1
    @24
    @26
    @22
    cH
    cK
    cW
    @32
    cdleme19.h
    lhpbase
    syl
    #
    @12
    cD
    cR
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
    cdleme19.d
    @12
    cK
    clat
    wcel
    #
    @34
    @22
    wcel
    #
    @24
    @35
    cW
    c.le
    wbr
    @12
    @0
    @36
    @25
    cK
    hllat
    syl
    @12
    @0
    @3
    @4
    @37
    @25
    @29
    @27
    cA
    @22
    c.or
    cK
    cR
    cS
    @32
    cdleme19.j
    cdleme19.a
    hlatjcl
    syl3anc
    @33
    @22
    cK
    c.le
    c.an
    @34
    cW
    @32
    cdleme19.l
    cdleme19.m
    latmle2
    syl3anc
    syl5eqbr
    cA
    @22
    cD
    c.or
    cK
    c.le
    c.an
    @13
    cW
    @32
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    atmod4i1
    syl131anc
    @12
    @17
    @19
    cW
    c.an
    @12
    cS
    cD
    c.or
    co
    #
    cT
    c.or
    co
    #
    @17
    @19
    @12
    @38
    @16
    cT
    c.or
    @12
    @0
    @1
    @3
    @4
    @5
    @38
    @16
    wceq
    @25
    @26
    @29
    @27
    @28
    cA
    cD
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
    cdleme19.d
    cdleme10
    syl212anc
    oveq1d
    @12
    @0
    @4
    @21
    @7
    @39
    @19
    wceq
    @25
    @27
    @30
    @31
    cA
    cS
    cD
    cT
    c.or
    cK
    cdleme19.j
    cdleme19.a
    hlatj32
    syl13anc
    eqtr3d
    oveq1d
    eqtr4d
    syl5eq
end
