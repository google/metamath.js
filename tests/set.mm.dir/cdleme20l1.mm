include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "clln.mm"
include "cfv.mm"
include "simp11l.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp22.mm"
include "simp23.mm"
include "jca.mm"
include "simp31.mm"
include "simp32.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "simp11r.mm"
include "simp21.mm"
include "simp33.mm"
include "cdlemeda.mm"
include "syl223anc.mm"
include "cdleme19c.mm"
include "syl233anc.mm"
include "eqid.mm"
include "llni2.mm"
include "syl31anc.mm"

theorem cdleme20l1
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( R e. A /\ S e. A /\ -. S .<_ W ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) ) -> ( F .\/ D ) e. ( LLines ` K ) )

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
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
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
    cP
    cQ
    wne
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
    w3a
    #
    w3a
    #
    @0
    cF
    cA
    wcel
    #
    cD
    cA
    wcel
    #
    cF
    cD
    wne
    #
    cF
    cD
    c.or
    co
    cK
    clln
    cfv
    #
    wcel
    @0
    @1
    @3
    @4
    @9
    @14
    simp11l
    #
    @15
    @2
    @3
    @4
    @7
    @8
    wa
    #
    @10
    @12
    @16
    @2
    @3
    @4
    @9
    @14
    simp11
    @2
    @3
    @4
    @9
    @14
    simp12
    #
    @2
    @3
    @4
    @9
    @14
    simp13
    #
    @15
    @7
    @8
    @5
    @6
    @7
    @8
    @14
    simp22
    #
    @5
    @6
    @7
    @8
    @14
    simp23
    #
    jca
    #
    @5
    @9
    @10
    @12
    @13
    simp31
    #
    @5
    @9
    @10
    @12
    @13
    simp32
    #
    cA
    cP
    cQ
    cS
    cU
    cF
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
    cdleme19.u
    cdleme19.f
    cdleme3fa
    syl132anc
    @15
    @0
    @1
    @7
    @8
    @6
    @13
    @12
    @17
    @20
    @0
    @1
    @3
    @4
    @9
    @14
    simp11r
    #
    @24
    @25
    @5
    @6
    @7
    @8
    @14
    simp21
    #
    @5
    @9
    @10
    @12
    @13
    simp33
    @28
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
    @15
    @0
    @1
    @3
    @4
    @21
    @6
    @10
    @12
    @18
    @20
    @29
    @22
    @23
    @26
    @30
    @27
    @28
    cA
    cD
    cP
    cQ
    cR
    cS
    cS
    cU
    cF
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cD
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.f
    cdleme19.d
    cdleme19.d
    cdleme19c
    syl233anc
    cA
    cF
    cD
    c.or
    cK
    @19
    cdleme19.j
    cdleme19.a
    @19
    eqid
    llni2
    syl31anc
end
