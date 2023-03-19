include "chlt.mm"
include "wcel.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wbr.mm"
include "eqid.mm"
include "isline3.mm"
include "biimp3a.mm"
include "simpl2r.mm"
include "simpl3l.mm"
include "necomd.mm"
include "simpr.mm"
include "neeqtrd.mm"
include "simpl11.mm"
include "simpl2l.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "simpl3r.mm"
include "breqtrrd.mm"
include "weq.mm"
include "neeq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "hlatlej1.mm"
include "pm2.61dane.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mpd.mm"

theorem lnatexN
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  assume lnatex.b: |- B = ( Base ` K )
  assume lnatex.l: |- .<_ = ( le ` K )
  assume lnatex.a: |- A = ( Atoms ` K )
  assume lnatex.n: |- N = ( Lines ` K )
  assume lnatex.m: |- M = ( pmap ` K )

  disjoint A q
  disjoint .<_ q
  disjoint P q
  disjoint X q
  disjoint q r
  disjoint q s
  disjoint r s
  disjoint A r
  disjoint A s
  disjoint B r
  disjoint B s
  disjoint K r
  disjoint K s
  disjoint .<_ r
  disjoint .<_ s
  disjoint M r
  disjoint M s
  disjoint N r
  disjoint N s
  disjoint P r
  disjoint P s
  disjoint X r
  disjoint X s
  assert |- ( ( K e. HL /\ X e. B /\ ( M ` X ) e. N ) -> E. q e. A ( q =/= P /\ q .<_ X ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    cM
    cfv
    cN
    wcel
    #
    w3a
    #
    vr
    cv
    #
    vs
    cv
    #
    wne
    #
    cX
    @4
    @5
    cK
    cjn
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vs
    cA
    wrex
    vr
    cA
    wrex
    #
    vq
    cv
    #
    cP
    wne
    #
    @12
    cX
    c.le
    wbr
    #
    wa
    #
    vq
    cA
    wrex
    #
    @0
    @1
    @2
    @11
    cA
    cB
    @7
    cK
    cM
    cN
    cX
    vs
    vr
    lnatex.b
    @7
    eqid
    #
    lnatex.a
    lnatex.n
    lnatex.m
    isline3
    biimp3a
    @3
    @10
    @16
    vr
    vs
    cA
    cA
    @3
    @4
    cA
    wcel
    #
    @5
    cA
    wcel
    #
    wa
    #
    @10
    @16
    @3
    @20
    @10
    w3a
    #
    @16
    @4
    cP
    @21
    @4
    cP
    wceq
    #
    wa
    #
    @19
    @5
    cP
    wne
    #
    @5
    cX
    c.le
    wbr
    #
    @16
    @18
    @19
    @3
    @10
    @22
    simpl2r
    #
    @23
    @5
    @4
    cP
    @23
    @4
    @5
    @6
    @9
    @3
    @20
    @22
    simpl3l
    necomd
    @21
    @22
    simpr
    neeqtrd
    @23
    @5
    @8
    cX
    c.le
    @23
    @0
    @18
    @19
    @5
    @8
    c.le
    wbr
    @0
    @1
    @2
    @20
    @10
    @22
    simpl11
    @18
    @19
    @3
    @10
    @22
    simpl2l
    @26
    cA
    @4
    @5
    @7
    cK
    c.le
    lnatex.l
    @17
    lnatex.a
    hlatlej2
    syl3anc
    @6
    @9
    @3
    @20
    @22
    simpl3r
    breqtrrd
    @15
    @24
    @25
    wa
    vq
    @5
    cA
    vq
    vs
    weq
    @13
    @24
    @14
    @25
    @12
    @5
    cP
    neeq1
    @12
    @5
    cX
    c.le
    breq1
    anbi12d
    rspcev
    syl12anc
    @21
    @4
    cP
    wne
    #
    wa
    #
    @18
    @27
    @4
    cX
    c.le
    wbr
    #
    @16
    @18
    @19
    @3
    @10
    @27
    simpl2l
    #
    @21
    @27
    simpr
    @28
    @4
    @8
    cX
    c.le
    @28
    @0
    @18
    @19
    @4
    @8
    c.le
    wbr
    @0
    @1
    @2
    @20
    @10
    @27
    simpl11
    @30
    @18
    @19
    @3
    @10
    @27
    simpl2r
    cA
    @4
    @5
    @7
    cK
    c.le
    lnatex.l
    @17
    lnatex.a
    hlatlej1
    syl3anc
    @6
    @9
    @3
    @20
    @27
    simpl3r
    breqtrrd
    @15
    @27
    @29
    wa
    vq
    @4
    cA
    vq
    vr
    weq
    @13
    @27
    @14
    @29
    @12
    @4
    cP
    neeq1
    @12
    @4
    cX
    c.le
    breq1
    anbi12d
    rspcev
    syl12anc
    pm2.61dane
    3exp
    rexlimdvv
    mpd
end
