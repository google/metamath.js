include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl3.mm"
include "cbs.mm"
include "wb.mm"
include "simpl1.mm"
include "eqid.mm"
include "llnbase.mm"
include "syl.mm"
include "islln3.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simp1r.mm"
include "simp3r.mm"
include "breqtrd.mm"
include "atcvrj2.mm"
include "syl132anc.mm"
include "breqtrrd.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mpd.mm"

theorem atcvrlln2
  let cA: class A
  let cC: class C
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vr: setvar r
  assume atcvrlln2.l: |- .<_ = ( le ` K )
  assume atcvrlln2.c: |- C = ( <o ` K )
  assume atcvrlln2.a: |- A = ( Atoms ` K )
  assume atcvrlln2.n: |- N = ( LLines ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ X e. N ) /\ P .<_ X ) -> P C X )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cX
    cN
    wcel
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
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
    @6
    @7
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
    @5
    @2
    @13
    @0
    @1
    @2
    @4
    simpl3
    #
    @5
    @0
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    @2
    @13
    wb
    @0
    @1
    @2
    @4
    simpl1
    @5
    @2
    @17
    @15
    @16
    cK
    cN
    cX
    @16
    eqid
    #
    atcvrlln2.n
    llnbase
    syl
    cA
    @16
    @9
    cK
    cN
    cX
    vr
    vq
    @18
    @9
    eqid
    #
    atcvrlln2.a
    atcvrlln2.n
    islln3
    syl2anc
    mpbid
    @5
    @12
    @14
    vq
    vr
    cA
    cA
    @5
    @6
    cA
    wcel
    #
    @7
    cA
    wcel
    #
    wa
    #
    @12
    @14
    @5
    @22
    @12
    w3a
    #
    cP
    @10
    cX
    cC
    @23
    @0
    @1
    @20
    @21
    @8
    cP
    @10
    c.le
    wbr
    cP
    @10
    cC
    wbr
    @0
    @1
    @2
    @4
    @22
    @12
    simp1l1
    @0
    @1
    @2
    @4
    @22
    @12
    simp1l2
    @5
    @20
    @21
    @12
    simp2l
    @5
    @20
    @21
    @12
    simp2r
    @5
    @22
    @8
    @11
    simp3l
    @23
    cP
    cX
    @10
    c.le
    @3
    @4
    @22
    @12
    simp1r
    @5
    @22
    @8
    @11
    simp3r
    #
    breqtrd
    cA
    cC
    cP
    @6
    @7
    @9
    cK
    c.le
    atcvrlln2.l
    @19
    atcvrlln2.c
    atcvrlln2.a
    atcvrj2
    syl132anc
    @24
    breqtrrd
    3exp
    rexlimdvv
    mpd
end
