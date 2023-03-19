include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp1.mm"
include "simp22.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "ltrncl.mm"
include "syl3anc.mm"
include "simp23.mm"
include "latjcl.mm"
include "simp21.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "trlcl.mm"
include "latmcl.mm"
include "syl5eqel.mm"

theorem cdlemkvcl
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
  let cV: class V
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
  assume cdlemk.v1: |- V = ( ( ( G ` P ) .\/ ( X ` P ) ) ./\ ( ( R ` ( G o. `' F ) ) .\/ ( R ` ( X o. `' F ) ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T /\ X e. T ) /\ P e. A ) -> V e. B )

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
    cX
    cT
    wcel
    #
    w3a
    #
    cP
    cA
    wcel
    #
    w3a
    #
    cV
    cP
    cG
    cfv
    #
    cP
    cX
    cfv
    #
    c.or
    co
    #
    cG
    cF
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    cX
    @12
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    cB
    cdlemk.v1
    @8
    cK
    clat
    wcel
    #
    @11
    cB
    wcel
    #
    @17
    cB
    wcel
    #
    @18
    cB
    wcel
    @8
    @0
    @19
    @0
    @1
    @6
    @7
    simp1l
    cK
    hllat
    syl
    #
    @8
    @19
    @9
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @20
    @22
    @8
    @2
    @4
    cP
    cB
    wcel
    #
    @23
    @2
    @6
    @7
    simp1
    #
    @2
    @3
    @4
    @5
    @7
    simp22
    #
    @7
    @2
    @25
    @6
    cA
    cB
    cP
    cK
    cdlemk.b
    cdlemk.a
    atbase
    3ad2ant3
    #
    cB
    cT
    cG
    cH
    cK
    chlt
    cW
    cP
    cdlemk.b
    cdlemk.h
    cdlemk.t
    ltrncl
    syl3anc
    @8
    @2
    @5
    @25
    @24
    @26
    @2
    @3
    @4
    @5
    @7
    simp23
    #
    @28
    cB
    cT
    cX
    cH
    cK
    chlt
    cW
    cP
    cdlemk.b
    cdlemk.h
    cdlemk.t
    ltrncl
    syl3anc
    cB
    c.or
    cK
    @9
    @10
    cdlemk.b
    cdlemk.j
    latjcl
    syl3anc
    @8
    @19
    @14
    cB
    wcel
    #
    @16
    cB
    wcel
    #
    @21
    @22
    @8
    @2
    @13
    cT
    wcel
    #
    @30
    @26
    @8
    @2
    @4
    @12
    cT
    wcel
    #
    @32
    @26
    @27
    @8
    @2
    @3
    @33
    @26
    @2
    @3
    @4
    @5
    @7
    simp21
    cT
    cF
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrncnv
    syl2anc
    #
    cT
    cG
    @12
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrnco
    syl3anc
    cB
    cR
    cT
    @13
    cH
    cK
    cW
    cdlemk.b
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcl
    syl2anc
    @8
    @2
    @15
    cT
    wcel
    #
    @31
    @26
    @8
    @2
    @5
    @33
    @35
    @26
    @29
    @34
    cT
    cX
    @12
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrnco
    syl3anc
    cB
    cR
    cT
    @15
    cH
    cK
    cW
    cdlemk.b
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcl
    syl2anc
    cB
    c.or
    cK
    @14
    @16
    cdlemk.b
    cdlemk.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    @11
    @17
    cdlemk.b
    cdlemk.m
    latmcl
    syl3anc
    syl5eqel
end
