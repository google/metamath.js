include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cdleme20d.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "simp22l.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmle1.mm"
include "syl5eqbr.mm"
include "eqbrtrd.mm"

theorem cdleme20e
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) /\ R .<_ ( P .\/ Q ) ) ) -> ( ( F .\/ G ) ./\ ( D .\/ Y ) ) .<_ ( S .\/ T ) )

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
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    cS
    cT
    wne
    wa
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
    @13
    c.le
    wbr
    wn
    wa
    cR
    @13
    c.le
    wbr
    w3a
    #
    w3a
    #
    cF
    cG
    c.or
    co
    cD
    cY
    c.or
    co
    c.an
    co
    cV
    cS
    cT
    c.or
    co
    #
    c.le
    cA
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cY
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.g
    cdleme19.d
    cdleme19.y
    cdleme20.v
    cdleme20d
    @15
    cV
    @16
    cW
    c.an
    co
    #
    @16
    c.le
    cdleme20.v
    @15
    cK
    clat
    wcel
    #
    @16
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @19
    wcel
    #
    @17
    @16
    c.le
    wbr
    @15
    @0
    @18
    @0
    @1
    @2
    @3
    @12
    @14
    simp11l
    #
    cK
    hllat
    syl
    @15
    @0
    @5
    @8
    @20
    @22
    @5
    @6
    @10
    @11
    @4
    @14
    simp21l
    @8
    @9
    @7
    @11
    @4
    @14
    simp22l
    cA
    @19
    c.or
    cK
    cS
    cT
    @19
    eqid
    #
    cdleme19.j
    cdleme19.a
    hlatjcl
    syl3anc
    @15
    @1
    @21
    @0
    @1
    @2
    @3
    @12
    @14
    simp11r
    @19
    cH
    cK
    cW
    @23
    cdleme19.h
    lhpbase
    syl
    @19
    cK
    c.le
    c.an
    @16
    cW
    @23
    cdleme19.l
    cdleme19.m
    latmle1
    syl3anc
    syl5eqbr
    eqbrtrd
end
