include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "lhpmcvr2.mm"
include "3adant3.mm"
include "simp3l.mm"
include "simp11.mm"
include "simp12.mm"
include "simp2.mm"
include "jca.mm"
include "simp13l.mm"
include "simp13r.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "simp12l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latlej1.mm"
include "simp3r.mm"
include "breqtrd.mm"
include "lhpmcvr4N.mm"
include "syl123anc.mm"
include "3jca.mm"
include "3expia.mm"
include "reximdva.mm"
include "mpd.mm"

theorem lhpmcvr5N
  let cA: class A
  let cB: class B
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume lhpmcvr2.b: |- B = ( Base ` K )
  assume lhpmcvr2.l: |- .<_ = ( le ` K )
  assume lhpmcvr2.j: |- .\/ = ( join ` K )
  assume lhpmcvr2.m: |- ./\ = ( meet ` K )
  assume lhpmcvr2.a: |- A = ( Atoms ` K )
  assume lhpmcvr2.h: |- H = ( LHyp ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint .<_ p
  disjoint ./\ p
  disjoint X p
  disjoint W p
  disjoint H p
  disjoint Y p
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( Y e. B /\ ( X ./\ Y ) .<_ W ) ) -> E. p e. A ( -. p .<_ W /\ -. p .<_ Y /\ ( p .\/ ( X ./\ W ) ) = X ) )

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
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cY
    cB
    wcel
    #
    cX
    cY
    c.an
    co
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @10
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    vp
    cA
    wrex
    #
    @11
    @10
    cY
    c.le
    wbr
    wn
    #
    @14
    w3a
    #
    vp
    cA
    wrex
    @2
    @5
    @16
    @8
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    vp
    lhpmcvr2.b
    lhpmcvr2.l
    lhpmcvr2.j
    lhpmcvr2.m
    lhpmcvr2.a
    lhpmcvr2.h
    lhpmcvr2
    3adant3
    @9
    @15
    @18
    vp
    cA
    @9
    @10
    cA
    wcel
    #
    @15
    @18
    @9
    @19
    @15
    w3a
    #
    @11
    @17
    @14
    @9
    @19
    @11
    @14
    simp3l
    #
    @20
    @2
    @5
    @19
    @11
    wa
    @6
    @7
    @10
    cX
    c.le
    wbr
    @17
    @2
    @5
    @8
    @19
    @15
    simp11
    @2
    @5
    @8
    @19
    @15
    simp12
    @20
    @19
    @11
    @9
    @19
    @15
    simp2
    @21
    jca
    @6
    @7
    @2
    @5
    @19
    @15
    simp13l
    @6
    @7
    @2
    @5
    @19
    @15
    simp13r
    @20
    @10
    @13
    cX
    c.le
    @20
    cK
    clat
    wcel
    #
    @10
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @10
    @13
    c.le
    wbr
    @20
    @0
    @22
    @0
    @1
    @5
    @8
    @19
    @15
    simp11l
    cK
    hllat
    syl
    #
    @19
    @9
    @23
    @15
    cA
    cB
    @10
    cK
    lhpmcvr2.b
    lhpmcvr2.a
    atbase
    3ad2ant2
    @20
    @22
    @3
    cW
    cB
    wcel
    #
    @24
    @25
    @3
    @4
    @2
    @8
    @19
    @15
    simp12l
    @20
    @1
    @26
    @0
    @1
    @5
    @8
    @19
    @15
    simp11r
    cB
    cH
    cK
    cW
    lhpmcvr2.b
    lhpmcvr2.h
    lhpbase
    syl
    cB
    cK
    c.an
    cX
    cW
    lhpmcvr2.b
    lhpmcvr2.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    c.le
    @10
    @12
    lhpmcvr2.b
    lhpmcvr2.l
    lhpmcvr2.j
    latlej1
    syl3anc
    @9
    @19
    @11
    @14
    simp3r
    #
    breqtrd
    cA
    cB
    @10
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    lhpmcvr2.b
    lhpmcvr2.l
    lhpmcvr2.j
    lhpmcvr2.m
    lhpmcvr2.a
    lhpmcvr2.h
    lhpmcvr4N
    syl123anc
    @27
    3jca
    3expia
    reximdva
    mpd
end
