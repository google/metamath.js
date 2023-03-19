include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cfv.mm"
include "wne.mm"
include "catm.mm"
include "eqid.mm"
include "trlnidatb.mm"
include "trlatn0.mm"
include "bitrd.mm"
include "necon4bid.mm"

theorem trlid0b
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let c.0: class .0.
  assume trlid0b.b: |- B = ( Base ` K )
  assume trlid0b.z: |- .0. = ( 0. ` K )
  assume trlid0b.h: |- H = ( LHyp ` K )
  assume trlid0b.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlid0b.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( F = ( _I |` B ) <-> ( R ` F ) = .0. ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cF
    cT
    wcel
    wa
    #
    cF
    cid
    cB
    cres
    #
    cF
    cR
    cfv
    #
    c.0
    @0
    cF
    @1
    wne
    @2
    cK
    catm
    cfv
    #
    wcel
    @2
    c.0
    wne
    @3
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    trlid0b.b
    @3
    eqid
    #
    trlid0b.h
    trlid0b.t
    trlid0b.r
    trlnidatb
    @3
    cR
    cT
    cF
    cH
    cK
    cW
    c.0
    trlid0b.z
    @4
    trlid0b.h
    trlid0b.t
    trlid0b.r
    trlatn0
    bitrd
    necon4bid
end
