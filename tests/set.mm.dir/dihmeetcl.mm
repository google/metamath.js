include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "ccnv.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "dihcnvid2.mm"
include "adantrr.mm"
include "adantrl.mm"
include "ineq12d.mm"
include "cmee.mm"
include "co.mm"
include "cbs.mm"
include "simpl.mm"
include "eqid.mm"
include "dihcnvcl.mm"
include "dihmeet.mm"
include "syl3anc.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "latmcl.mm"
include "dihcl.mm"
include "syldan.mm"
include "eqeltrrd.mm"

theorem dihmeetcl
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihmeetcl.h: |- H = ( LHyp ` K )
  assume dihmeetcl.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. ran I /\ Y e. ran I ) ) -> ( X i^i Y ) e. ran I )

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
    cX
    cI
    crn
    #
    wcel
    #
    cY
    @3
    wcel
    #
    wa
    #
    wa
    #
    cX
    cI
    ccnv
    #
    cfv
    #
    cI
    cfv
    #
    cY
    @8
    cfv
    #
    cI
    cfv
    #
    cin
    #
    cX
    cY
    cin
    @3
    @7
    @10
    cX
    @12
    cY
    @2
    @4
    @10
    cX
    wceq
    @5
    cH
    cI
    cK
    cW
    cX
    dihmeetcl.h
    dihmeetcl.i
    dihcnvid2
    adantrr
    @2
    @5
    @12
    cY
    wceq
    @4
    cH
    cI
    cK
    cW
    cY
    dihmeetcl.h
    dihmeetcl.i
    dihcnvid2
    adantrl
    ineq12d
    @7
    @9
    @11
    cK
    cmee
    cfv
    #
    co
    #
    cI
    cfv
    #
    @13
    @3
    @7
    @2
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    @11
    @17
    wcel
    #
    @16
    @13
    wceq
    @2
    @6
    simpl
    @2
    @4
    @18
    @5
    @17
    cH
    cI
    cK
    cW
    cX
    @17
    eqid
    #
    dihmeetcl.h
    dihmeetcl.i
    dihcnvcl
    adantrr
    #
    @2
    @5
    @19
    @4
    @17
    cH
    cI
    cK
    cW
    cY
    @20
    dihmeetcl.h
    dihmeetcl.i
    dihcnvcl
    adantrl
    #
    @17
    cH
    cI
    cK
    @14
    cW
    @9
    @11
    @20
    @14
    eqid
    #
    dihmeetcl.h
    dihmeetcl.i
    dihmeet
    syl3anc
    @2
    @6
    @15
    @17
    wcel
    #
    @16
    @3
    wcel
    @7
    cK
    clat
    wcel
    #
    @18
    @19
    @24
    @0
    @25
    @1
    @6
    cK
    hllat
    ad2antrr
    @21
    @22
    @17
    cK
    @14
    @9
    @11
    @20
    @23
    latmcl
    syl3anc
    @17
    cH
    cI
    cK
    cW
    @15
    @20
    dihmeetcl.h
    dihmeetcl.i
    dihcl
    syldan
    eqeltrrd
    eqeltrrd
end
