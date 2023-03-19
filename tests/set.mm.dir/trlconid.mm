include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "catm.mm"
include "eqid.mm"
include "trlcoat.mm"
include "wb.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "trlnidatb.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem trlconid
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume trlconid.b: |- B = ( Base ` K )
  assume trlconid.h: |- H = ( LHyp ` K )
  assume trlconid.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlconid.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( R ` F ) =/= ( R ` G ) ) -> ( F o. G ) =/= ( _I |` B ) )

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
    cG
    cT
    wcel
    #
    wa
    #
    cF
    cR
    cfv
    cG
    cR
    cfv
    wne
    #
    w3a
    #
    cF
    cG
    ccom
    #
    cid
    cB
    cres
    wne
    #
    @6
    cR
    cfv
    cK
    catm
    cfv
    #
    wcel
    #
    @8
    cR
    cT
    cF
    cG
    cH
    cK
    cW
    @8
    eqid
    #
    trlconid.h
    trlconid.t
    trlconid.r
    trlcoat
    @5
    @0
    @6
    cT
    wcel
    #
    @7
    @9
    wb
    @0
    @3
    @4
    simp1
    #
    @5
    @0
    @1
    @2
    @11
    @12
    @0
    @1
    @2
    @4
    simp2l
    @0
    @1
    @2
    @4
    simp2r
    cT
    cF
    cG
    cH
    cK
    cW
    trlconid.h
    trlconid.t
    ltrnco
    syl3anc
    @8
    cB
    cR
    cT
    @6
    cH
    cK
    cW
    trlconid.b
    @10
    trlconid.h
    trlconid.t
    trlconid.r
    trlnidatb
    syl2anc
    mpbird
end
