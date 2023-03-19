include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cdlemf.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1rl.mm"
include "eqeltrd.mm"
include "wb.mm"
include "simp1l.mm"
include "simp2.mm"
include "trlnidatb.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "jca.mm"
include "3expia.mm"
include "reximdva.mm"
include "mpd.mm"

theorem cdlemfnid
  let cA: class A
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume cdlemfnid.b: |- B = ( Base ` K )
  assume cdlemfnid.l: |- .<_ = ( le ` K )
  assume cdlemfnid.a: |- A = ( Atoms ` K )
  assume cdlemfnid.h: |- H = ( LHyp ` K )
  assume cdlemfnid.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemfnid.r: |- R = ( ( trL ` K ) ` W )

  disjoint A f
  disjoint H f
  disjoint K f
  disjoint .<_ f
  disjoint T f
  disjoint U f
  disjoint W f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. A /\ U .<_ W ) ) -> E. f e. T ( ( R ` f ) = U /\ f =/= ( _I |` B ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cA
    wcel
    #
    cU
    cW
    c.le
    wbr
    #
    wa
    #
    wa
    #
    vf
    cv
    #
    cR
    cfv
    #
    cU
    wceq
    #
    vf
    cT
    wrex
    @7
    @5
    cid
    cB
    cres
    wne
    #
    wa
    #
    vf
    cT
    wrex
    cA
    cR
    cT
    cU
    vf
    cH
    cK
    c.le
    cW
    cdlemfnid.l
    cdlemfnid.a
    cdlemfnid.h
    cdlemfnid.t
    cdlemfnid.r
    cdlemf
    @4
    @7
    @9
    vf
    cT
    @4
    @5
    cT
    wcel
    #
    @7
    @9
    @4
    @10
    @7
    w3a
    #
    @7
    @8
    @4
    @10
    @7
    simp3
    #
    @11
    @8
    @6
    cA
    wcel
    #
    @11
    @6
    cU
    cA
    @12
    @1
    @2
    @0
    @10
    @7
    simp1rl
    eqeltrd
    @11
    @0
    @10
    @8
    @13
    wb
    @0
    @3
    @10
    @7
    simp1l
    @4
    @10
    @7
    simp2
    cA
    cB
    cR
    cT
    @5
    cH
    cK
    cW
    cdlemfnid.b
    cdlemfnid.a
    cdlemfnid.h
    cdlemfnid.t
    cdlemfnid.r
    trlnidatb
    syl2anc
    mpbird
    jca
    3expia
    reximdva
    mpd
end
