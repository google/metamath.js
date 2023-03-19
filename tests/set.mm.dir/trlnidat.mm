include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wrex.mm"
include "eqid.mm"
include "ltrnnid.mm"
include "simp11.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp12.mm"
include "simp3r.mm"
include "trlat.mm"
include "syl122anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem trlnidat
  let cA: class A
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let vp: setvar p
  assume trlnidat.b: |- B = ( Base ` K )
  assume trlnidat.a: |- A = ( Atoms ` K )
  assume trlnidat.h: |- H = ( LHyp ` K )
  assume trlnidat.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlnidat.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ F =/= ( _I |` B ) ) -> ( R ` F ) e. A )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    cF
    cid
    cB
    cres
    wne
    #
    w3a
    #
    vp
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    @4
    cF
    cfv
    @4
    wne
    #
    wa
    #
    vp
    cA
    wrex
    cF
    cR
    cfv
    cA
    wcel
    #
    cA
    cB
    cT
    cF
    cH
    cK
    @5
    cW
    vp
    trlnidat.b
    @5
    eqid
    #
    trlnidat.a
    trlnidat.h
    trlnidat.t
    ltrnnid
    @3
    @8
    @9
    vp
    cA
    @3
    @4
    cA
    wcel
    #
    @8
    w3a
    @0
    @11
    @6
    @1
    @7
    @9
    @0
    @1
    @2
    @11
    @8
    simp11
    @3
    @11
    @8
    simp2
    @3
    @11
    @6
    @7
    simp3l
    @0
    @1
    @2
    @11
    @8
    simp12
    @3
    @11
    @6
    @7
    simp3r
    cA
    @4
    cR
    cT
    cF
    cH
    cK
    @5
    cW
    @10
    trlnidat.a
    trlnidat.h
    trlnidat.t
    trlnidat.r
    trlat
    syl122anc
    rexlimdv3a
    mpd
end
