include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cfv.mm"
include "wceq.mm"
include "ctrl.mm"
include "cp0.mm"
include "cple.mm"
include "wbr.mm"
include "cltrn.mm"
include "eqid.mm"
include "idltrn.mm"
include "adantr.mm"
include "tendotp.mm"
include "mpd3an3.mm"
include "trlid0.mm"
include "breqtrd.mm"
include "cops.mm"
include "wb.mm"
include "hlop.mm"
include "ad2antrr.mm"
include "tendocl.mm"
include "trlcl.mm"
include "syldan.mm"
include "ople0.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "trlid0b.mm"
include "mpbird.mm"

theorem tendoid
  let cB: class B
  let cS: class S
  let cE: class E
  let cH: class H
  let cK: class K
  let cW: class W
  assume tendoid.b: |- B = ( Base ` K )
  assume tendoid.h: |- H = ( LHyp ` K )
  assume tendoid.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ S e. E ) -> ( S ` ( _I |` B ) ) = ( _I |` B ) )

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
    cS
    cE
    wcel
    #
    wa
    #
    cid
    cB
    cres
    #
    cS
    cfv
    #
    @5
    wceq
    #
    @6
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    #
    cK
    cp0
    cfv
    #
    wceq
    #
    @4
    @9
    @10
    cK
    cple
    cfv
    #
    wbr
    #
    @11
    @4
    @9
    @5
    @8
    cfv
    #
    @10
    @12
    @2
    @3
    @5
    cW
    cK
    cltrn
    cfv
    cfv
    #
    wcel
    #
    @9
    @14
    @12
    wbr
    @2
    @16
    @3
    cB
    @15
    cH
    cK
    cW
    tendoid.b
    tendoid.h
    @15
    eqid
    #
    idltrn
    adantr
    #
    @8
    cS
    @15
    cE
    @5
    cH
    cK
    @12
    chlt
    cW
    @12
    eqid
    #
    tendoid.h
    @17
    @8
    eqid
    #
    tendoid.e
    tendotp
    mpd3an3
    @2
    @14
    @10
    wceq
    @3
    cB
    @8
    cH
    cK
    cW
    @10
    tendoid.b
    @10
    eqid
    #
    tendoid.h
    @20
    trlid0
    adantr
    breqtrd
    @4
    cK
    cops
    wcel
    #
    @9
    cB
    wcel
    #
    @13
    @11
    wb
    @0
    @22
    @1
    @3
    cK
    hlop
    ad2antrr
    @2
    @3
    @6
    @15
    wcel
    #
    @23
    @2
    @3
    @16
    @24
    @18
    cS
    @15
    cE
    @5
    cH
    cK
    chlt
    cW
    tendoid.h
    @17
    tendoid.e
    tendocl
    mpd3an3
    #
    cB
    @8
    @15
    @6
    cH
    cK
    cW
    tendoid.b
    tendoid.h
    @17
    @20
    trlcl
    syldan
    cB
    cK
    @12
    @9
    @10
    tendoid.b
    @19
    @21
    ople0
    syl2anc
    mpbid
    @2
    @3
    @24
    @7
    @11
    wb
    @25
    cB
    @8
    @15
    @6
    cH
    cK
    cW
    @10
    tendoid.b
    @21
    tendoid.h
    @17
    @20
    trlid0b
    syldan
    mpbird
end
