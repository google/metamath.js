include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "w3a.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp31.mm"
include "simp2l.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "wne.mm"
include "simp1r.mm"
include "simp2r.mm"
include "simp32.mm"
include "simp33.mm"
include "cdlemesner.mm"
include "syl122anc.mm"
include "lhpat.mm"
include "syl222anc.mm"
include "eqeltrd.mm"
include "syl5eqel.mm"

theorem cdlemeda
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemeda.l: |- .<_ = ( le ` K )
  assume cdlemeda.j: |- .\/ = ( join ` K )
  assume cdlemeda.m: |- ./\ = ( meet ` K )
  assume cdlemeda.a: |- A = ( Atoms ` K )
  assume cdlemeda.h: |- H = ( LHyp ` K )
  assume cdlemeda.d: |- D = ( ( R .\/ S ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S e. A /\ -. S .<_ W ) /\ ( R e. A /\ R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> D e. A )

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
    cR
    cA
    wcel
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cS
    @7
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
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
    cA
    cdlemeda.d
    @11
    @13
    cS
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    cA
    @11
    @12
    @14
    cW
    c.an
    @11
    @0
    @6
    @3
    @12
    @14
    wceq
    @0
    @1
    @5
    @10
    simp1l
    #
    @2
    @5
    @6
    @8
    @9
    simp31
    #
    @2
    @3
    @4
    @10
    simp2l
    #
    cA
    c.or
    cK
    cR
    cS
    cdlemeda.j
    cdlemeda.a
    hlatjcom
    syl3anc
    oveq1d
    @11
    @0
    @1
    @3
    @4
    @6
    cS
    cR
    wne
    #
    @15
    cA
    wcel
    @16
    @0
    @1
    @5
    @10
    simp1r
    @18
    @2
    @3
    @4
    @10
    simp2r
    @17
    @11
    @0
    @6
    @3
    @8
    @9
    @19
    @16
    @17
    @18
    @2
    @5
    @6
    @8
    @9
    simp32
    @2
    @5
    @6
    @8
    @9
    simp33
    cA
    cP
    cQ
    cR
    cS
    cH
    c.or
    cK
    c.le
    cdlemeda.l
    cdlemeda.j
    cdlemeda.a
    cdlemeda.h
    cdlemesner
    syl122anc
    cA
    cS
    cR
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemeda.l
    cdlemeda.j
    cdlemeda.m
    cdlemeda.a
    cdlemeda.h
    lhpat
    syl222anc
    eqeltrd
    syl5eqel
end
