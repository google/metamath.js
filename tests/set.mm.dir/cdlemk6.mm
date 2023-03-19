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
include "simp31.mm"
include "simp32.mm"
include "simp33l.mm"
include "3jca.mm"
include "cdlemk5.mm"
include "syld3an3.mm"
include "wi.mm"
include "simp11l.mm"
include "simp22l.mm"
include "simp11.mm"
include "simp13.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simp21r.mm"
include "simp21l.mm"
include "simp12.mm"
include "trlcocnvat.mm"
include "syl121anc.mm"
include "simp33r.mm"
include "dalaw.mm"
include "syl133anc.mm"
include "mpd.mm"

theorem cdlemk6
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cX: class X
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( ( N e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ ( ( R ` G ) =/= ( R ` F ) /\ ( R ` X ) =/= ( R ` F ) ) ) ) -> ( ( P .\/ ( G ` P ) ) ./\ ( ( N ` P ) .\/ ( R ` ( G o. `' F ) ) ) ) .<_ ( ( ( ( G ` P ) .\/ ( X ` P ) ) ./\ ( ( R ` ( G o. `' F ) ) .\/ ( R ` ( X o. `' F ) ) ) ) .\/ ( ( ( X ` P ) .\/ P ) ./\ ( ( R ` ( X o. `' F ) ) .\/ ( N ` P ) ) ) ) )

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
    cX
    cT
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
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
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
    @15
    wne
    #
    cG
    cR
    cfv
    @12
    wne
    #
    cX
    cR
    cfv
    @12
    wne
    #
    wa
    #
    w3a
    #
    w3a
    #
    cP
    cP
    cN
    cfv
    #
    c.or
    co
    cP
    cG
    cfv
    #
    cG
    cF
    ccnv
    #
    ccom
    cR
    cfv
    #
    c.or
    co
    c.an
    co
    cP
    cX
    cfv
    #
    cX
    @25
    ccom
    cR
    cfv
    #
    c.or
    co
    c.le
    wbr
    #
    cP
    @24
    c.or
    co
    @23
    @26
    c.or
    co
    c.an
    co
    @24
    @27
    c.or
    co
    @26
    @28
    c.or
    co
    c.an
    co
    @27
    cP
    c.or
    co
    @28
    @23
    c.or
    co
    c.an
    co
    c.or
    co
    c.le
    wbr
    #
    @5
    @14
    @21
    @16
    @17
    @18
    w3a
    @29
    @22
    @16
    @17
    @18
    @5
    @14
    @16
    @17
    @20
    simp31
    @5
    @14
    @16
    @17
    @20
    simp32
    @18
    @19
    @16
    @17
    @5
    @14
    simp33l
    #
    3jca
    cA
    cB
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cX
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    cdlemk5
    syld3an3
    @22
    @0
    @9
    @24
    cA
    wcel
    #
    @27
    cA
    wcel
    #
    @23
    cA
    wcel
    #
    @26
    cA
    wcel
    #
    @28
    cA
    wcel
    #
    @29
    @30
    wi
    @0
    @1
    @3
    @4
    @14
    @21
    simp11l
    @9
    @10
    @8
    @13
    @5
    @21
    simp22l
    #
    @22
    @2
    @4
    @9
    @32
    @2
    @3
    @4
    @14
    @21
    simp11
    #
    @2
    @3
    @4
    @14
    @21
    simp13
    #
    @37
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnat
    syl3anc
    @22
    @2
    @7
    @9
    @33
    @38
    @6
    @7
    @11
    @13
    @5
    @21
    simp21r
    #
    @37
    cA
    cP
    cT
    cX
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnat
    syl3anc
    @22
    @2
    @6
    @9
    @34
    @38
    @6
    @7
    @11
    @13
    @5
    @21
    simp21l
    @37
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
    ltrnat
    syl3anc
    @22
    @2
    @4
    @3
    @18
    @35
    @38
    @39
    @2
    @3
    @4
    @14
    @21
    simp12
    #
    @31
    cA
    cR
    cT
    cG
    cF
    cH
    cK
    cW
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcocnvat
    syl121anc
    @22
    @2
    @7
    @3
    @19
    @36
    @38
    @40
    @41
    @18
    @19
    @16
    @17
    @5
    @14
    simp33r
    cA
    cR
    cT
    cX
    cF
    cH
    cK
    cW
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcocnvat
    syl121anc
    cA
    cP
    @24
    @27
    @23
    @26
    @28
    c.or
    cK
    c.le
    c.an
    cdlemk.l
    cdlemk.j
    cdlemk.m
    cdlemk.a
    dalaw
    syl133anc
    mpd
end
