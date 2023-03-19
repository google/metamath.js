include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "simp3l.mm"
include "cp0.mm"
include "wb.mm"
include "simp1.mm"
include "simp2l.mm"
include "eqid.mm"
include "trlid0b.mm"
include "syl2anc.mm"
include "biimpar.mm"
include "simp3r.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "simpl1.mm"
include "simpl2r.mm"
include "mpbird.mm"
include "eqtr4d.mm"
include "ex.mm"
include "sylbid.mm"
include "necon3d.mm"
include "mpd.mm"

theorem trlnid
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume trlnid.b: |- B = ( Base ` K )
  assume trlnid.h: |- H = ( LHyp ` K )
  assume trlnid.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlnid.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( F =/= G /\ ( R ` F ) = ( R ` G ) ) ) -> F =/= ( _I |` B ) )

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
    cG
    wne
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    wceq
    #
    wa
    #
    w3a
    #
    @4
    cF
    cid
    cB
    cres
    #
    wne
    @0
    @3
    @4
    @7
    simp3l
    @9
    cF
    @10
    cF
    cG
    @9
    cF
    @10
    wceq
    #
    @5
    cK
    cp0
    cfv
    #
    wceq
    #
    cF
    cG
    wceq
    #
    @9
    @0
    @1
    @11
    @13
    wb
    @0
    @3
    @8
    simp1
    @0
    @1
    @2
    @8
    simp2l
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    @12
    trlnid.b
    @12
    eqid
    #
    trlnid.h
    trlnid.t
    trlnid.r
    trlid0b
    syl2anc
    #
    @9
    @13
    @14
    @9
    @13
    wa
    #
    cF
    @10
    cG
    @9
    @11
    @13
    @16
    biimpar
    @17
    cG
    @10
    wceq
    #
    @6
    @12
    wceq
    #
    @9
    @13
    @19
    @9
    @5
    @6
    @12
    @0
    @3
    @4
    @7
    simp3r
    eqeq1d
    biimpa
    @17
    @0
    @2
    @18
    @19
    wb
    @0
    @3
    @8
    @13
    simpl1
    @1
    @2
    @0
    @8
    @13
    simpl2r
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    @12
    trlnid.b
    @15
    trlnid.h
    trlnid.t
    trlnid.r
    trlid0b
    syl2anc
    mpbird
    eqtr4d
    ex
    sylbid
    necon3d
    mpd
end
