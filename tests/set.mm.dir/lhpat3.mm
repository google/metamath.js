include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "w3a.mm"
include "wceq.mm"
include "simpl3r.mm"
include "simpr.mm"
include "wb.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1ll.mm"
include "hllat.mm"
include "syl.mm"
include "simp2r.mm"
include "eqid.mm"
include "atbase.mm"
include "simp1rl.mm"
include "simp2l.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1lr.mm"
include "lhpbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "adantr.mm"
include "mpbi2and.mm"
include "syl6breqr.mm"
include "cal.mm"
include "hlatl.mm"
include "simpl2r.mm"
include "simpl1l.mm"
include "simpl1r.mm"
include "simpl2l.mm"
include "simpl3l.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "atcmp.mm"
include "mpbid.mm"
include "ex.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "necon3bbid.mm"

theorem lhpat3
  let cA: class A
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
  assume lhpat.l: |- .<_ = ( le ` K )
  assume lhpat.j: |- .\/ = ( join ` K )
  assume lhpat.m: |- ./\ = ( meet ` K )
  assume lhpat.a: |- A = ( Atoms ` K )
  assume lhpat.h: |- H = ( LHyp ` K )
  assume lhpat2.r: |- R = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) ) /\ ( Q e. A /\ S e. A ) /\ ( P =/= Q /\ S .<_ ( P .\/ Q ) ) ) -> ( -. S .<_ W <-> S =/= R ) )

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
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    wa
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
    #
    wa
    #
    w3a
    #
    cS
    cW
    c.le
    wbr
    #
    cS
    cR
    @14
    @15
    cS
    cR
    wceq
    #
    @14
    @15
    @16
    @14
    @15
    wa
    #
    cS
    cR
    c.le
    wbr
    #
    @16
    @17
    cS
    @11
    cW
    c.an
    co
    #
    cR
    c.le
    @17
    @12
    @15
    cS
    @19
    c.le
    wbr
    #
    @10
    @12
    @6
    @9
    @15
    simpl3r
    @14
    @15
    simpr
    @14
    @12
    @15
    wa
    @20
    wb
    #
    @15
    @14
    cK
    clat
    wcel
    #
    cS
    cK
    cbs
    cfv
    #
    wcel
    #
    @11
    @23
    wcel
    #
    cW
    @23
    wcel
    #
    @21
    @14
    @0
    @22
    @0
    @1
    @5
    @9
    @13
    simp1ll
    #
    cK
    hllat
    syl
    #
    @14
    @8
    @24
    @6
    @7
    @8
    @13
    simp2r
    cA
    @23
    cS
    cK
    @23
    eqid
    #
    lhpat.a
    atbase
    syl
    @14
    @0
    @3
    @7
    @25
    @27
    @3
    @4
    @2
    @9
    @13
    simp1rl
    @6
    @7
    @8
    @13
    simp2l
    cA
    @23
    c.or
    cK
    cP
    cQ
    @29
    lhpat.j
    lhpat.a
    hlatjcl
    syl3anc
    #
    @14
    @1
    @26
    @0
    @1
    @5
    @9
    @13
    simp1lr
    @23
    cH
    cK
    cW
    @29
    lhpat.h
    lhpbase
    syl
    #
    @23
    cK
    c.le
    c.an
    cS
    @11
    cW
    @29
    lhpat.l
    lhpat.m
    latlem12
    syl13anc
    adantr
    mpbi2and
    lhpat2.r
    syl6breqr
    @17
    cK
    cal
    wcel
    #
    @8
    cR
    cA
    wcel
    #
    @18
    @16
    wb
    @17
    @0
    @32
    @14
    @0
    @15
    @27
    adantr
    cK
    hlatl
    syl
    @7
    @8
    @6
    @13
    @15
    simpl2r
    @17
    @2
    @5
    @7
    @10
    @33
    @2
    @5
    @9
    @13
    @15
    simpl1l
    @2
    @5
    @9
    @13
    @15
    simpl1r
    @7
    @8
    @6
    @13
    @15
    simpl2l
    @10
    @12
    @6
    @9
    @15
    simpl3l
    cA
    cP
    cQ
    cR
    cH
    c.or
    cK
    c.le
    c.an
    cW
    lhpat.l
    lhpat.j
    lhpat.m
    lhpat.a
    lhpat.h
    lhpat2.r
    lhpat2
    syl112anc
    cA
    cS
    cR
    cK
    c.le
    lhpat.l
    lhpat.a
    atcmp
    syl3anc
    mpbid
    ex
    @14
    @15
    @16
    cR
    cW
    c.le
    wbr
    @14
    cR
    @19
    cW
    c.le
    lhpat2.r
    @14
    @22
    @25
    @26
    @19
    cW
    c.le
    wbr
    @28
    @30
    @31
    @23
    cK
    c.le
    c.an
    @11
    cW
    @29
    lhpat.l
    lhpat.m
    latmle2
    syl3anc
    syl5eqbr
    cS
    cR
    cW
    c.le
    breq1
    syl5ibrcom
    impbid
    necon3bbid
end
