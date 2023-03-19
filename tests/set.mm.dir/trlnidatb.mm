include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cfv.mm"
include "trlnidat.mm"
include "3expia.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "wi.mm"
include "wrex.mm"
include "eqid.mm"
include "lhpexnle.mm"
include "adantr.mm"
include "wb.mm"
include "ltrnideq.mm"
include "3expa.mm"
include "cp0.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp2.mm"
include "simp1r.mm"
include "simp3.mm"
include "trl0.mm"
include "syl112anc.mm"
include "cal.mm"
include "simplll.mm"
include "hlatl.mm"
include "atn0.mm"
include "ex.mm"
include "3syl.mm"
include "necon2bd.mm"
include "syld.mm"
include "sylbid.mm"
include "rexlimddv.mm"
include "necon2ad.mm"
include "impbid.mm"

theorem trlnidatb
  let cA: class A
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let vp: setvar p
  assume trlnidatb.b: |- B = ( Base ` K )
  assume trlnidatb.a: |- A = ( Atoms ` K )
  assume trlnidatb.h: |- H = ( LHyp ` K )
  assume trlnidatb.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlnidatb.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( F =/= ( _I |` B ) <-> ( R ` F ) e. A ) )

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
    cF
    cT
    wcel
    #
    wa
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cF
    cR
    cfv
    #
    cA
    wcel
    #
    @2
    @3
    @6
    @8
    cA
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    trlnidatb.b
    trlnidatb.a
    trlnidatb.h
    trlnidatb.t
    trlnidatb.r
    trlnidat
    3expia
    @4
    @8
    cF
    @5
    @4
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
    cF
    @5
    wceq
    #
    @8
    wn
    #
    wi
    vp
    cA
    @2
    @11
    vp
    cA
    wrex
    @3
    cA
    cH
    cK
    @10
    cW
    vp
    @10
    eqid
    #
    trlnidatb.a
    trlnidatb.h
    lhpexnle
    adantr
    @4
    @9
    cA
    wcel
    @11
    wa
    #
    wa
    #
    @12
    @9
    cF
    cfv
    @9
    wceq
    #
    @13
    @2
    @3
    @15
    @12
    @17
    wb
    cA
    cB
    @9
    cT
    cF
    cH
    cK
    @10
    cW
    trlnidatb.b
    @14
    trlnidatb.a
    trlnidatb.h
    trlnidatb.t
    ltrnideq
    3expa
    @16
    @17
    @7
    cK
    cp0
    cfv
    #
    wceq
    #
    @13
    @4
    @15
    @17
    @19
    @4
    @15
    @17
    w3a
    @2
    @15
    @3
    @17
    @19
    @2
    @3
    @15
    @17
    simp1l
    @4
    @15
    @17
    simp2
    @2
    @3
    @15
    @17
    simp1r
    @4
    @15
    @17
    simp3
    cA
    @9
    cR
    cT
    cF
    cH
    cK
    @10
    cW
    @18
    @14
    @18
    eqid
    #
    trlnidatb.a
    trlnidatb.h
    trlnidatb.t
    trlnidatb.r
    trl0
    syl112anc
    3expia
    @16
    @8
    @7
    @18
    @16
    @0
    cK
    cal
    wcel
    #
    @8
    @7
    @18
    wne
    #
    wi
    @0
    @1
    @3
    @15
    simplll
    cK
    hlatl
    @21
    @8
    @22
    cA
    @7
    cK
    @18
    @20
    trlnidatb.a
    atn0
    ex
    3syl
    necon2bd
    syld
    sylbid
    rexlimddv
    necon2ad
    impbid
end
