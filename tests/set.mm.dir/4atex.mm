include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simp21l.mm"
include "ad2antrr.mm"
include "simp21r.mm"
include "oveq1.mm"
include "eqcoms.mm"
include "adantl.mm"
include "breq1.mm"
include "notbid.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "simpl3r.mm"
include "wb.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "cbvrexv.mm"
include "syl6rbbr.mm"
include "mpbid.mm"
include "simp22l.mm"
include "ad3antrrr.mm"
include "simp22r.mm"
include "simp3l.mm"
include "necomd.mm"
include "simpr.mm"
include "simpllr.mm"
include "clc.mm"
include "wi.mm"
include "simp1l.mm"
include "hlcvl.mm"
include "syl.mm"
include "simp23.mm"
include "simplr.mm"
include "cvlatexch1.mm"
include "syl131anc.mm"
include "mpd.mm"
include "cvlsupr2.mm"
include "mpbir3and.mm"
include "pm2.61dane.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "4atexlem7.mm"
include "syl113anc.mm"
include "pm2.61dan.mm"

theorem 4atex
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vr: setvar r
  assume 4that.l: |- .<_ = ( le ` K )
  assume 4that.j: |- .\/ = ( join ` K )
  assume 4that.a: |- A = ( Atoms ` K )
  assume 4that.h: |- H = ( LHyp ` K )

  disjoint r z
  disjoint A r
  disjoint A z
  disjoint H r
  disjoint .\/ r
  disjoint .\/ z
  disjoint K r
  disjoint K z
  disjoint .<_ r
  disjoint .<_ z
  disjoint P r
  disjoint P z
  disjoint Q r
  disjoint Q z
  disjoint S r
  disjoint S z
  disjoint W r
  disjoint W z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ S e. A ) /\ ( P =/= Q /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( P .\/ z ) = ( S .\/ z ) ) )

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
    #
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cS
    cA
    wcel
    #
    w3a
    #
    cP
    cQ
    wne
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    cP
    @14
    c.or
    co
    #
    cQ
    @14
    c.or
    co
    #
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    #
    wa
    #
    w3a
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
    vz
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    cP
    @26
    c.or
    co
    #
    cS
    @26
    c.or
    co
    #
    wceq
    #
    wa
    #
    vz
    cA
    wrex
    #
    @23
    @25
    wa
    #
    @33
    cS
    cP
    @34
    cS
    cP
    wceq
    #
    wa
    @3
    @5
    cP
    cP
    c.or
    co
    #
    cS
    cP
    c.or
    co
    #
    wceq
    #
    @33
    @23
    @3
    @25
    @35
    @3
    @5
    @10
    @11
    @2
    @22
    simp21l
    #
    ad2antrr
    @23
    @5
    @25
    @35
    @3
    @5
    @10
    @11
    @2
    @22
    simp21r
    ad2antrr
    @35
    @38
    @34
    @38
    cP
    cS
    cP
    cS
    cP
    c.or
    oveq1
    eqcoms
    adantl
    @32
    @5
    @38
    wa
    vz
    cP
    cA
    @26
    cP
    wceq
    #
    @28
    @5
    @31
    @38
    @40
    @27
    @4
    @26
    cP
    cW
    c.le
    breq1
    notbid
    @40
    @29
    @36
    @30
    @37
    @26
    cP
    cP
    c.or
    oveq2
    @26
    cP
    cS
    c.or
    oveq2
    eqeq12d
    anbi12d
    rspcev
    syl12anc
    @34
    cS
    cP
    wne
    #
    wa
    #
    @33
    cS
    cQ
    @42
    cS
    cQ
    wceq
    #
    wa
    @21
    @33
    @34
    @21
    @41
    @43
    @13
    @21
    @2
    @12
    @25
    simpl3r
    ad2antrr
    @43
    @21
    @33
    wb
    @42
    @43
    @33
    @28
    @29
    cQ
    @26
    c.or
    co
    #
    wceq
    #
    wa
    #
    vz
    cA
    wrex
    @21
    @43
    @32
    @46
    vz
    cA
    @43
    @31
    @45
    @28
    @43
    @30
    @44
    @29
    cS
    cQ
    @26
    c.or
    oveq1
    eqeq2d
    anbi2d
    rexbidv
    @20
    @46
    vr
    vz
    cA
    @14
    @26
    wceq
    #
    @16
    @28
    @19
    @45
    @47
    @15
    @27
    @14
    @26
    cW
    c.le
    breq1
    notbid
    @47
    @17
    @29
    @18
    @44
    @14
    @26
    cP
    c.or
    oveq2
    @14
    @26
    cQ
    c.or
    oveq2
    eqeq12d
    anbi12d
    cbvrexv
    syl6rbbr
    adantl
    mpbid
    @42
    cS
    cQ
    wne
    #
    wa
    #
    @7
    @9
    @24
    cS
    cQ
    c.or
    co
    #
    wceq
    #
    @33
    @23
    @7
    @25
    @41
    @48
    @7
    @9
    @6
    @11
    @2
    @22
    simp22l
    ad3antrrr
    #
    @23
    @9
    @25
    @41
    @48
    @7
    @9
    @6
    @11
    @2
    @22
    simp22r
    ad3antrrr
    @49
    @51
    cQ
    cP
    wne
    #
    cQ
    cS
    wne
    #
    cQ
    cP
    cS
    c.or
    co
    c.le
    wbr
    #
    @23
    @53
    @25
    @41
    @48
    @23
    cP
    cQ
    @2
    @12
    @13
    @21
    simp3l
    necomd
    ad3antrrr
    @49
    cS
    cQ
    @42
    @48
    simpr
    necomd
    @49
    @25
    @55
    @23
    @25
    @41
    @48
    simpllr
    @49
    cK
    clc
    wcel
    #
    @11
    @7
    @3
    @41
    @25
    @55
    wi
    @23
    @56
    @25
    @41
    @48
    @23
    @0
    @56
    @0
    @1
    @12
    @22
    simp1l
    cK
    hlcvl
    syl
    ad3antrrr
    #
    @23
    @11
    @25
    @41
    @48
    @2
    @6
    @10
    @11
    @22
    simp23
    ad3antrrr
    #
    @52
    @23
    @3
    @25
    @41
    @48
    @39
    ad3antrrr
    #
    @34
    @41
    @48
    simplr
    #
    cA
    cS
    cQ
    cP
    c.or
    cK
    c.le
    4that.l
    4that.j
    4that.a
    cvlatexch1
    syl131anc
    mpd
    @49
    @56
    @3
    @11
    @7
    cP
    cS
    wne
    @51
    @53
    @54
    @55
    w3a
    wb
    @57
    @59
    @58
    @52
    @49
    cS
    cP
    @60
    necomd
    cA
    cP
    cS
    cQ
    c.or
    cK
    c.le
    4that.a
    4that.l
    4that.j
    cvlsupr2
    syl131anc
    mpbir3and
    @32
    @9
    @51
    wa
    vz
    cQ
    cA
    @26
    cQ
    wceq
    #
    @28
    @9
    @31
    @51
    @61
    @27
    @8
    @26
    cQ
    cW
    c.le
    breq1
    notbid
    @61
    @29
    @24
    @30
    @50
    @26
    cQ
    cP
    c.or
    oveq2
    @26
    cQ
    cS
    c.or
    oveq2
    eqeq12d
    anbi12d
    rspcev
    syl12anc
    pm2.61dane
    pm2.61dane
    @23
    @25
    wn
    #
    wa
    @2
    @12
    @13
    @62
    @21
    @33
    @2
    @12
    @22
    @62
    simpl1
    @2
    @12
    @22
    @62
    simpl2
    @13
    @21
    @2
    @12
    @62
    simpl3l
    @23
    @62
    simpr
    @13
    @21
    @2
    @12
    @62
    simpl3r
    vz
    cA
    cP
    cQ
    cS
    cH
    c.or
    cK
    c.le
    cW
    vr
    4that.l
    4that.j
    4that.a
    4that.h
    4atexlem7
    syl113anc
    pm2.61dan
end
