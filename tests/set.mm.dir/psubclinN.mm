include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "club.mm"
include "cfv.mm"
include "cmee.mm"
include "co.mm"
include "cpmap.mm"
include "cin.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1.mm"
include "ccla.mm"
include "wss.mm"
include "hlclat.mm"
include "3ad2ant1.mm"
include "catm.mm"
include "eqid.mm"
include "psubclssatN.mm"
include "3adant3.mm"
include "atssbase.mm"
include "syl6ss.mm"
include "clatlubcl.mm"
include "syl2anc.mm"
include "3adant2.mm"
include "pmapmeet.mm"
include "syl3anc.mm"
include "pmapidclN.mm"
include "ineq12d.mm"
include "eqtrd.mm"
include "clat.mm"
include "hllat.mm"
include "latmcl.mm"
include "pmapsubclN.mm"
include "eqeltrrd.mm"

theorem psubclinN
  let cC: class C
  let cK: class K
  let cX: class X
  let cY: class Y
  assume psubclin.c: |- C = ( PSubCl ` K )


  assert |- ( ( K e. HL /\ X e. C /\ Y e. C ) -> ( X i^i Y ) e. C )

  proof
    cK
    chlt
    wcel
    #
    cX
    cC
    wcel
    #
    cY
    cC
    wcel
    #
    w3a
    #
    cX
    cK
    club
    cfv
    #
    cfv
    #
    cY
    @4
    cfv
    #
    cK
    cmee
    cfv
    #
    co
    #
    cK
    cpmap
    cfv
    #
    cfv
    #
    cX
    cY
    cin
    #
    cC
    @3
    @10
    @5
    @9
    cfv
    #
    @6
    @9
    cfv
    #
    cin
    #
    @11
    @3
    @0
    @5
    cK
    cbs
    cfv
    #
    wcel
    #
    @6
    @15
    wcel
    #
    @10
    @14
    wceq
    @0
    @1
    @2
    simp1
    #
    @3
    cK
    ccla
    wcel
    #
    cX
    @15
    wss
    @16
    @0
    @1
    @19
    @2
    cK
    hlclat
    3ad2ant1
    #
    @3
    cX
    cK
    catm
    cfv
    #
    @15
    @0
    @1
    cX
    @21
    wss
    @2
    @21
    cC
    chlt
    cK
    cX
    @21
    eqid
    #
    psubclin.c
    psubclssatN
    3adant3
    @21
    @15
    cK
    @15
    eqid
    #
    @22
    atssbase
    #
    syl6ss
    @15
    cX
    @4
    cK
    @23
    @4
    eqid
    #
    clatlubcl
    syl2anc
    #
    @3
    @19
    cY
    @15
    wss
    @17
    @20
    @3
    cY
    @21
    @15
    @0
    @2
    cY
    @21
    wss
    @1
    @21
    cC
    chlt
    cK
    cY
    @22
    psubclin.c
    psubclssatN
    3adant2
    @24
    syl6ss
    @15
    cY
    @4
    cK
    @23
    @25
    clatlubcl
    syl2anc
    #
    @21
    @15
    @9
    cK
    @7
    @5
    @6
    @23
    @7
    eqid
    #
    @22
    @9
    eqid
    #
    pmapmeet
    syl3anc
    @3
    @12
    cX
    @13
    cY
    @0
    @1
    @12
    cX
    wceq
    @2
    cC
    @4
    cK
    @9
    cX
    @25
    @29
    psubclin.c
    pmapidclN
    3adant3
    @0
    @2
    @13
    cY
    wceq
    @1
    cC
    @4
    cK
    @9
    cY
    @25
    @29
    psubclin.c
    pmapidclN
    3adant2
    ineq12d
    eqtrd
    @3
    @0
    @8
    @15
    wcel
    #
    @10
    cC
    wcel
    @18
    @3
    cK
    clat
    wcel
    #
    @16
    @17
    @30
    @0
    @1
    @31
    @2
    cK
    hllat
    3ad2ant1
    @26
    @27
    @15
    cK
    @7
    @5
    @6
    @23
    @28
    latmcl
    syl3anc
    @15
    cC
    cK
    @9
    @8
    @23
    @29
    psubclin.c
    pmapsubclN
    syl2anc
    eqeltrrd
end
