include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "cal.mm"
include "hlatl.mm"
include "ad3antrrr.mm"
include "atn0.mm"
include "sylancom.mm"
include "ex.mm"
include "wceq.mm"
include "trlator0.mm"
include "ord.mm"
include "necon1ad.mm"
include "impbid.mm"

theorem trlatn0
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( ( R ` F ) e. A <-> ( R ` F ) =/= .0. ) )

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
    cA
    wcel
    #
    @4
    c.0
    wne
    #
    @3
    @5
    @6
    @3
    @5
    cK
    cal
    wcel
    #
    @6
    @0
    @7
    @1
    @2
    @5
    cK
    hlatl
    ad3antrrr
    cA
    @4
    cK
    c.0
    trl0a.z
    trl0a.a
    atn0
    sylancom
    ex
    @3
    @5
    @4
    c.0
    @3
    @5
    @4
    c.0
    wceq
    cA
    cR
    cT
    cF
    cH
    cK
    cW
    c.0
    trl0a.z
    trl0a.a
    trl0a.h
    trl0a.t
    trl0a.r
    trlator0
    ord
    necon1ad
    impbid
end
