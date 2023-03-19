include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wrex.mm"
include "eqid.mm"
include "lhpexnle.mm"
include "ad2antrr.mm"
include "simplll.mm"
include "simpr.mm"
include "simpllr.mm"
include "simplr.mm"
include "adantr.mm"
include "trl0.mm"
include "syl112anc.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"
include "trlat.mm"
include "rexlimddv.mm"
include "syl5bir.mm"
include "orrd.mm"
include "orcomd.mm"

theorem trlator0
  let cA: class A
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let vp: setvar p
  assume trl0a.z: |- .0. = ( 0. ` K )
  assume trl0a.a: |- A = ( Atoms ` K )
  assume trl0a.h: |- H = ( LHyp ` K )
  assume trl0a.t: |- T = ( ( LTrn ` K ) ` W )
  assume trl0a.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( ( R ` F ) e. A \/ ( R ` F ) = .0. ) )

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
    wa
    #
    cF
    cR
    cfv
    #
    c.0
    wceq
    #
    @3
    cA
    wcel
    #
    @2
    @4
    @5
    @4
    wn
    @3
    c.0
    wne
    #
    @2
    @5
    @3
    c.0
    df-ne
    @2
    @6
    @5
    @2
    @6
    wa
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
    @5
    vp
    cA
    @0
    @10
    vp
    cA
    wrex
    @1
    @6
    cA
    cH
    cK
    @9
    cW
    vp
    @9
    eqid
    #
    trl0a.a
    trl0a.h
    lhpexnle
    ad2antrr
    @7
    @8
    cA
    wcel
    @10
    wa
    #
    wa
    #
    @0
    @12
    @1
    @8
    cF
    cfv
    #
    @8
    wne
    #
    @5
    @0
    @1
    @6
    @12
    simplll
    #
    @7
    @12
    simpr
    @0
    @1
    @6
    @12
    simpllr
    #
    @13
    @6
    @15
    @2
    @6
    @12
    simplr
    @13
    @14
    @8
    @3
    c.0
    @13
    @14
    @8
    wceq
    #
    @4
    @13
    @18
    wa
    @0
    @12
    @1
    @18
    @4
    @13
    @0
    @18
    @16
    adantr
    @7
    @12
    @18
    simplr
    @13
    @1
    @18
    @17
    adantr
    @13
    @18
    simpr
    cA
    @8
    cR
    cT
    cF
    cH
    cK
    @9
    cW
    c.0
    @11
    trl0a.z
    trl0a.a
    trl0a.h
    trl0a.t
    trl0a.r
    trl0
    syl112anc
    ex
    necon3d
    mpd
    cA
    @8
    cR
    cT
    cF
    cH
    cK
    @9
    cW
    @11
    trl0a.a
    trl0a.h
    trl0a.t
    trl0a.r
    trlat
    syl112anc
    rexlimddv
    ex
    syl5bir
    orrd
    orcomd
end
