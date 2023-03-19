include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simprl.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "eqid.mm"
include "isline3.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp1l1.mm"
include "simp1l3.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp1rr.mm"
include "simp3r.mm"
include "breqtrd.mm"
include "atcvrj2.mm"
include "syl132anc.mm"
include "breqtrrd.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mpd.mm"

theorem lncvrat
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vr: setvar r
  assume lncvrat.b: |- B = ( Base ` K )
  assume lncvrat.l: |- .<_ = ( le ` K )
  assume lncvrat.c: |- C = ( <o ` K )
  assume lncvrat.a: |- A = ( Atoms ` K )
  assume lncvrat.n: |- N = ( Lines ` K )
  assume lncvrat.m: |- M = ( pmap ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ P e. A ) /\ ( ( M ` X ) e. N /\ P .<_ X ) ) -> P C X )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    #
    cX
    cM
    cfv
    cN
    wcel
    #
    cP
    cX
    c.le
    wbr
    #
    wa
    #
    wa
    #
    vq
    cv
    #
    vr
    cv
    #
    wne
    #
    cX
    @8
    @9
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
    vr
    cA
    wrex
    vq
    cA
    wrex
    #
    cP
    cX
    cC
    wbr
    #
    @7
    @4
    @15
    @3
    @4
    @5
    simprl
    @7
    @0
    @1
    @4
    @15
    wb
    @0
    @1
    @2
    @6
    simpl1
    @0
    @1
    @2
    @6
    simpl2
    cA
    cB
    @11
    cK
    cM
    cN
    cX
    vr
    vq
    lncvrat.b
    @11
    eqid
    #
    lncvrat.a
    lncvrat.n
    lncvrat.m
    isline3
    syl2anc
    mpbid
    @7
    @14
    @16
    vq
    vr
    cA
    cA
    @7
    @8
    cA
    wcel
    #
    @9
    cA
    wcel
    #
    wa
    #
    @14
    @16
    @7
    @20
    @14
    w3a
    #
    cP
    @12
    cX
    cC
    @21
    @0
    @2
    @18
    @19
    @10
    cP
    @12
    c.le
    wbr
    cP
    @12
    cC
    wbr
    @0
    @1
    @2
    @6
    @20
    @14
    simp1l1
    @0
    @1
    @2
    @6
    @20
    @14
    simp1l3
    @7
    @18
    @19
    @14
    simp2l
    @7
    @18
    @19
    @14
    simp2r
    @7
    @20
    @10
    @13
    simp3l
    @21
    cP
    cX
    @12
    c.le
    @4
    @5
    @3
    @20
    @14
    simp1rr
    @7
    @20
    @10
    @13
    simp3r
    #
    breqtrd
    cA
    cC
    cP
    @8
    @9
    @11
    cK
    c.le
    lncvrat.l
    @17
    lncvrat.c
    lncvrat.a
    atcvrj2
    syl132anc
    @22
    breqtrrd
    3exp
    rexlimdvv
    mpd
end
