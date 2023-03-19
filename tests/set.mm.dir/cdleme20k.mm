include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wne.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2r.mm"
include "simp2l.mm"
include "simp3r.mm"
include "simp3l.mm"
include "cdlemednpq.mm"
include "syl133anc.mm"
include "wceq.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp11r.mm"
include "simp2ll.mm"
include "eqid.mm"
include "cdleme1b.mm"
include "syl23anc.mm"
include "simp2rl.mm"
include "cdlemedb.mm"
include "syl22anc.mm"
include "latlej2.mm"
include "syl3anc.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem cdleme20k
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ P e. A /\ Q e. A ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) ) -> ( F .\/ D ) =/= ( P .\/ Q ) )

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
    cQ
    cA
    wcel
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
    wa
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
    @13
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cD
    @13
    c.le
    wbr
    #
    wn
    #
    cF
    cD
    c.or
    co
    #
    @13
    wne
    @17
    @2
    @3
    @4
    @11
    @8
    @15
    @14
    @19
    @2
    @3
    @4
    @12
    @16
    simp11
    @2
    @3
    @4
    @12
    @16
    simp12
    #
    @2
    @3
    @4
    @12
    @16
    simp13
    #
    @5
    @8
    @11
    @16
    simp2r
    @5
    @8
    @11
    @16
    simp2l
    @5
    @12
    @14
    @15
    simp3r
    @5
    @12
    @14
    @15
    simp3l
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
    cdlemednpq
    syl133anc
    @17
    @18
    @20
    @13
    @17
    cD
    @20
    c.le
    wbr
    #
    @20
    @13
    wceq
    @18
    @17
    cK
    clat
    wcel
    #
    cF
    cK
    cbs
    cfv
    #
    wcel
    #
    cD
    @25
    wcel
    #
    @23
    @17
    @0
    @24
    @0
    @1
    @3
    @4
    @12
    @16
    simp11l
    #
    cK
    hllat
    syl
    @17
    @0
    @1
    @3
    @4
    @6
    @26
    @28
    @0
    @1
    @3
    @4
    @12
    @16
    simp11r
    #
    @21
    @22
    @6
    @7
    @11
    @5
    @16
    simp2ll
    #
    cA
    @25
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
    @25
    eqid
    #
    cdleme1b
    syl23anc
    @17
    @0
    @1
    @9
    @6
    @27
    @28
    @29
    @9
    @10
    @8
    @5
    @16
    simp2rl
    @30
    cA
    @25
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
    @31
    cdlemedb
    syl22anc
    @25
    c.or
    cK
    c.le
    cF
    cD
    @31
    cdleme19.l
    cdleme19.j
    latlej2
    syl3anc
    @20
    @13
    cD
    c.le
    breq2
    syl5ibcom
    necon3bd
    mpd
end
