include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "wceq.mm"
include "wo.mm"
include "co.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl2r.mm"
include "simpl3.mm"
include "lhp2atnle.mm"
include "syl121anc.mm"
include "simp3r.mm"
include "simp12r.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "neneqd.mm"
include "cal.mm"
include "wb.mm"
include "simp11l.mm"
include "hlatl.mm"
include "syl.mm"
include "simp3l.mm"
include "simp12l.mm"
include "atcmp.mm"
include "syl3anc.mm"
include "mtbird.mm"
include "adantr.mm"
include "oveq2.mm"
include "col.mm"
include "cbs.mm"
include "cfv.mm"
include "hlol.mm"
include "eqid.mm"
include "atbase.mm"
include "olj01.mm"
include "sylan9eqr.mm"
include "breq2d.mm"
include "simp2l.mm"
include "mpjaodan.mm"

theorem lhp2at0nle
  let cA: class A
  let cP: class P
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lhp2at0nle.l: |- .<_ = ( le ` K )
  assume lhp2at0nle.j: |- .\/ = ( join ` K )
  assume lhp2at0nle.z: |- .0. = ( 0. ` K )
  assume lhp2at0nle.a: |- A = ( Atoms ` K )
  assume lhp2at0nle.h: |- H = ( LHyp ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ U =/= V ) /\ ( ( U e. A \/ U = .0. ) /\ U .<_ W ) /\ ( V e. A /\ V .<_ W ) ) -> -. V .<_ ( P .\/ U ) )

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
    cU
    cV
    wne
    #
    w3a
    #
    cU
    cA
    wcel
    #
    cU
    c.0
    wceq
    #
    wo
    #
    cU
    cW
    c.le
    wbr
    #
    wa
    #
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    @8
    cV
    cP
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @9
    @16
    @8
    wa
    @7
    @8
    @11
    @15
    @19
    @7
    @12
    @15
    @8
    simpl1
    @16
    @8
    simpr
    @10
    @11
    @7
    @15
    @8
    simpl2r
    @7
    @12
    @15
    @8
    simpl3
    cA
    cP
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    lhp2at0nle.l
    lhp2at0nle.j
    lhp2at0nle.a
    lhp2at0nle.h
    lhp2atnle
    syl121anc
    @16
    @9
    wa
    #
    @18
    cV
    cP
    c.le
    wbr
    #
    @16
    @21
    wn
    @9
    @16
    @21
    cV
    cP
    wceq
    #
    @16
    cV
    cP
    @16
    @14
    @4
    cV
    cP
    wne
    @7
    @12
    @13
    @14
    simp3r
    @3
    @4
    @2
    @6
    @12
    @15
    simp12r
    cV
    cP
    cW
    c.le
    nbrne2
    syl2anc
    neneqd
    @16
    cK
    cal
    wcel
    #
    @13
    @3
    @21
    @22
    wb
    @16
    @0
    @23
    @0
    @1
    @5
    @6
    @12
    @15
    simp11l
    #
    cK
    hlatl
    syl
    @7
    @12
    @13
    @14
    simp3l
    @3
    @4
    @2
    @6
    @12
    @15
    simp12l
    #
    cA
    cV
    cP
    cK
    c.le
    lhp2at0nle.l
    lhp2at0nle.a
    atcmp
    syl3anc
    mtbird
    adantr
    @20
    @17
    cP
    cV
    c.le
    @9
    @16
    @17
    cP
    c.0
    c.or
    co
    #
    cP
    cU
    c.0
    cP
    c.or
    oveq2
    @16
    cK
    col
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @26
    cP
    wceq
    @16
    @0
    @27
    @24
    cK
    hlol
    syl
    @16
    @3
    @29
    @25
    cA
    @28
    cP
    cK
    @28
    eqid
    #
    lhp2at0nle.a
    atbase
    syl
    @28
    c.or
    cK
    cP
    c.0
    @30
    lhp2at0nle.j
    lhp2at0nle.z
    olj01
    syl2anc
    sylan9eqr
    breq2d
    mtbird
    @7
    @10
    @11
    @15
    simp2l
    mpjaodan
end
