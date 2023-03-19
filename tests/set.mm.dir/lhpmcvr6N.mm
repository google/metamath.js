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
include "lhpmcvr5N.mm"
include "simp31.mm"
include "simp32.mm"
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
include "simp33.mm"
include "breqtrd.mm"
include "3jca.mm"
include "3expia.mm"
include "reximdva.mm"
include "mpd.mm"

theorem lhpmcvr6N
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( Y e. B /\ ( X ./\ Y ) .<_ W ) ) -> E. p e. A ( -. p .<_ W /\ -. p .<_ Y /\ p .<_ X ) )

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
    cX
    cY
    c.an
    co
    cW
    c.le
    wbr
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
    @8
    cY
    c.le
    wbr
    wn
    #
    @8
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
    w3a
    #
    vp
    cA
    wrex
    @9
    @10
    @8
    cX
    c.le
    wbr
    #
    w3a
    #
    vp
    cA
    wrex
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    vp
    lhpmcvr2.b
    lhpmcvr2.l
    lhpmcvr2.j
    lhpmcvr2.m
    lhpmcvr2.a
    lhpmcvr2.h
    lhpmcvr5N
    @7
    @14
    @16
    vp
    cA
    @7
    @8
    cA
    wcel
    #
    @14
    @16
    @7
    @17
    @14
    w3a
    #
    @9
    @10
    @15
    @7
    @17
    @9
    @10
    @13
    simp31
    @7
    @17
    @9
    @10
    @13
    simp32
    @18
    @8
    @12
    cX
    c.le
    @18
    cK
    clat
    wcel
    #
    @8
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @8
    @12
    c.le
    wbr
    @18
    @0
    @19
    @0
    @1
    @5
    @6
    @17
    @14
    simp11l
    cK
    hllat
    syl
    #
    @17
    @7
    @20
    @14
    cA
    cB
    @8
    cK
    lhpmcvr2.b
    lhpmcvr2.a
    atbase
    3ad2ant2
    @18
    @19
    @3
    cW
    cB
    wcel
    #
    @21
    @22
    @3
    @4
    @2
    @6
    @17
    @14
    simp12l
    @18
    @1
    @23
    @0
    @1
    @5
    @6
    @17
    @14
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
    @8
    @11
    lhpmcvr2.b
    lhpmcvr2.l
    lhpmcvr2.j
    latlej1
    syl3anc
    @7
    @17
    @9
    @10
    @13
    simp33
    breqtrd
    3jca
    3expia
    reximdva
    mpd
end
