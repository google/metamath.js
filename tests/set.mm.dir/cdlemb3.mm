include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wceq.mm"
include "wne.mm"
include "simpl1.mm"
include "simpl2.mm"
include "cdlemg5.mm"
include "syl2anc.mm"
include "wb.mm"
include "ancom.mm"
include "eqcom.mm"
include "simp2.mm"
include "oveq2d.mm"
include "simp11l.mm"
include "simp12l.mm"
include "hlatjidm.mm"
include "eqtr3d.mm"
include "breq2d.mm"
include "cal.mm"
include "hlatl.mm"
include "syl.mm"
include "simp3.mm"
include "atcmp.mm"
include "syl3anc.mm"
include "bitr2d.mm"
include "syl5bb.mm"
include "necon3abid.mm"
include "anbi2d.mm"
include "3expa.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "simpl3.mm"
include "simpr.mm"
include "cdlemb2.mm"
include "syl121anc.mm"
include "pm2.61dane.mm"

theorem cdlemb3
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vr: setvar r
  let vq: setvar q
  assume cdlemg5.l: |- .<_ = ( le ` K )
  assume cdlemg5.j: |- .\/ = ( join ` K )
  assume cdlemg5.a: |- A = ( Atoms ` K )
  assume cdlemg5.h: |- H = ( LHyp ` K )

  disjoint A r
  disjoint H r
  disjoint K r
  disjoint .<_ r
  disjoint P r
  disjoint W r
  disjoint .\/ r
  disjoint Q r
  disjoint q r
  disjoint A q
  disjoint H q
  disjoint K q
  disjoint .<_ q
  disjoint P q
  disjoint W q
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> E. r e. A ( -. r .<_ W /\ -. r .<_ ( P .\/ Q ) ) )

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
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @8
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    wa
    #
    vr
    cA
    wrex
    #
    cP
    cQ
    @7
    cP
    cQ
    wceq
    #
    wa
    #
    cP
    @8
    wne
    #
    @9
    wa
    #
    vr
    cA
    wrex
    #
    @14
    @16
    @2
    @5
    @19
    @2
    @5
    @6
    @15
    simpl1
    @2
    @5
    @6
    @15
    simpl2
    cA
    cP
    cH
    c.or
    cK
    c.le
    cW
    vr
    cdlemg5.l
    cdlemg5.j
    cdlemg5.a
    cdlemg5.h
    cdlemg5
    syl2anc
    @16
    @18
    @13
    vr
    cA
    @7
    @15
    @8
    cA
    wcel
    #
    @18
    @13
    wb
    @18
    @9
    @17
    wa
    @7
    @15
    @20
    w3a
    #
    @13
    @17
    @9
    ancom
    @21
    @17
    @12
    @9
    @21
    @11
    cP
    @8
    cP
    @8
    wceq
    @8
    cP
    wceq
    #
    @21
    @11
    cP
    @8
    eqcom
    @21
    @11
    @8
    cP
    c.le
    wbr
    #
    @22
    @21
    @10
    cP
    @8
    c.le
    @21
    cP
    cP
    c.or
    co
    #
    @10
    cP
    @21
    cP
    cQ
    cP
    c.or
    @7
    @15
    @20
    simp2
    oveq2d
    @21
    @0
    @3
    @24
    cP
    wceq
    @0
    @1
    @5
    @6
    @15
    @20
    simp11l
    #
    @3
    @4
    @2
    @6
    @15
    @20
    simp12l
    #
    cA
    c.or
    cK
    cP
    cdlemg5.j
    cdlemg5.a
    hlatjidm
    syl2anc
    eqtr3d
    breq2d
    @21
    cK
    cal
    wcel
    #
    @20
    @3
    @23
    @22
    wb
    @21
    @0
    @27
    @25
    cK
    hlatl
    syl
    @7
    @15
    @20
    simp3
    @26
    cA
    @8
    cP
    cK
    c.le
    cdlemg5.l
    cdlemg5.a
    atcmp
    syl3anc
    bitr2d
    syl5bb
    necon3abid
    anbi2d
    syl5bb
    3expa
    rexbidva
    mpbid
    @7
    cP
    cQ
    wne
    #
    wa
    @2
    @5
    @6
    @28
    @14
    @2
    @5
    @6
    @28
    simpl1
    @2
    @5
    @6
    @28
    simpl2
    @2
    @5
    @6
    @28
    simpl3
    @7
    @28
    simpr
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    cW
    vr
    cdlemg5.l
    cdlemg5.j
    cdlemg5.a
    cdlemg5.h
    cdlemb2
    syl121anc
    pm2.61dane
end
