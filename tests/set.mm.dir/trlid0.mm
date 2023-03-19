include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "catm.mm"
include "eqid.mm"
include "lhpexnle.mm"
include "cltrn.mm"
include "simpl.mm"
include "simpr.mm"
include "idltrn.mm"
include "adantr.mm"
include "wb.mm"
include "ltrnideq.mm"
include "syl3anc.mm"
include "mpbii.mm"
include "trl0.mm"
include "syl112anc.mm"
include "rexlimddv.mm"

theorem trlid0
  let cB: class B
  let cR: class R
  let cH: class H
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let vp: setvar p
  assume trlid0.b: |- B = ( Base ` K )
  assume trlid0.z: |- .0. = ( 0. ` K )
  assume trlid0.h: |- H = ( LHyp ` K )
  assume trlid0.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> ( R ` ( _I |` B ) ) = .0. )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cid
    cB
    cres
    #
    cR
    cfv
    c.0
    wceq
    #
    vp
    cK
    catm
    cfv
    #
    @6
    cH
    cK
    @2
    cW
    vp
    @2
    eqid
    #
    @6
    eqid
    #
    trlid0.h
    lhpexnle
    @0
    @1
    @6
    wcel
    @3
    wa
    #
    wa
    #
    @0
    @9
    @4
    cW
    cK
    cltrn
    cfv
    cfv
    #
    wcel
    #
    @1
    @4
    cfv
    @1
    wceq
    #
    @5
    @0
    @9
    simpl
    #
    @0
    @9
    simpr
    #
    @0
    @12
    @9
    cB
    @11
    cH
    cK
    cW
    trlid0.b
    trlid0.h
    @11
    eqid
    #
    idltrn
    adantr
    #
    @10
    @4
    @4
    wceq
    #
    @13
    @4
    eqid
    @10
    @0
    @12
    @9
    @18
    @13
    wb
    @14
    @17
    @15
    @6
    cB
    @1
    @11
    @4
    cH
    cK
    @2
    cW
    trlid0.b
    @7
    @8
    trlid0.h
    @16
    ltrnideq
    syl3anc
    mpbii
    @6
    @1
    cR
    @11
    @4
    cH
    cK
    @2
    cW
    c.0
    @7
    trlid0.z
    @8
    trlid0.h
    @16
    trlid0.r
    trl0
    syl112anc
    rexlimddv
end
