include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp2l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latmle2.mm"
include "lattrd.mm"
include "syl5eqbr.mm"

theorem cdleme23a
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let cX: class X
  assume cdleme23.b: |- B = ( Base ` K )
  assume cdleme23.l: |- .<_ = ( le ` K )
  assume cdleme23.j: |- .\/ = ( join ` K )
  assume cdleme23.m: |- ./\ = ( meet ` K )
  assume cdleme23.a: |- A = ( Atoms ` K )
  assume cdleme23.h: |- H = ( LHyp ` K )
  assume cdleme23.v: |- V = ( ( S .\/ T ) ./\ ( X ./\ W ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( X e. B /\ -. X .<_ W ) /\ ( S =/= T /\ ( S .\/ ( X ./\ W ) ) = X /\ ( T .\/ ( X ./\ W ) ) = X ) ) -> V .<_ W )

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
    w3a
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
    cS
    cT
    wne
    cS
    cX
    cW
    c.an
    co
    #
    c.or
    co
    cX
    wceq
    cT
    @13
    c.or
    co
    cX
    wceq
    w3a
    #
    w3a
    #
    cV
    cS
    cT
    c.or
    co
    #
    @13
    c.an
    co
    #
    cW
    c.le
    cdleme23.v
    @15
    cB
    cK
    c.le
    @17
    @13
    cW
    cdleme23.b
    cdleme23.l
    @15
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @5
    @8
    @12
    @14
    simp11l
    #
    cK
    hllat
    syl
    #
    @15
    @18
    @16
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @17
    cB
    wcel
    @20
    @15
    @0
    @3
    @6
    @21
    @19
    @3
    @4
    @2
    @8
    @12
    @14
    simp12l
    @6
    @7
    @2
    @5
    @12
    @14
    simp13l
    cA
    cB
    c.or
    cK
    cS
    cT
    cdleme23.b
    cdleme23.j
    cdleme23.a
    hlatjcl
    syl3anc
    #
    @15
    @18
    @10
    cW
    cB
    wcel
    #
    @22
    @20
    @9
    @10
    @11
    @14
    simp2l
    #
    @15
    @1
    @24
    @0
    @1
    @5
    @8
    @12
    @14
    simp11r
    cB
    cH
    cK
    cW
    cdleme23.b
    cdleme23.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    cX
    cW
    cdleme23.b
    cdleme23.m
    latmcl
    syl3anc
    #
    cB
    cK
    c.an
    @16
    @13
    cdleme23.b
    cdleme23.m
    latmcl
    syl3anc
    @27
    @26
    @15
    @18
    @21
    @22
    @17
    @13
    c.le
    wbr
    @20
    @23
    @27
    cB
    cK
    c.le
    c.an
    @16
    @13
    cdleme23.b
    cdleme23.l
    cdleme23.m
    latmle2
    syl3anc
    @15
    @18
    @10
    @24
    @13
    cW
    c.le
    wbr
    @20
    @25
    @26
    cB
    cK
    c.le
    c.an
    cX
    cW
    cdleme23.b
    cdleme23.l
    cdleme23.m
    latmle2
    syl3anc
    lattrd
    syl5eqbr
end
