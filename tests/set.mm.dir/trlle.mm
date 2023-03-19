include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "coc.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "catm.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "eqid.mm"
include "lhpocnel.mm"
include "adantr.mm"
include "trlval2.mm"
include "mpd3an3.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "cops.mm"
include "hlop.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "ltrncl.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "latmle2.mm"
include "eqbrtrd.mm"

theorem trlle
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume trlle.l: |- .<_ = ( le ` K )
  assume trlle.h: |- H = ( LHyp ` K )
  assume trlle.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlle.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( R ` F ) .<_ W )

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
    cR
    cfv
    #
    cW
    cK
    coc
    cfv
    #
    cfv
    #
    @7
    cF
    cfv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cW
    c.le
    @2
    @3
    @7
    cK
    catm
    cfv
    #
    wcel
    @7
    cW
    c.le
    wbr
    wn
    wa
    #
    @5
    @12
    wceq
    @2
    @14
    @3
    @13
    cH
    cK
    c.le
    @6
    cW
    trlle.l
    @6
    eqid
    #
    @13
    eqid
    #
    trlle.h
    lhpocnel
    adantr
    @13
    @7
    cR
    cT
    cF
    cH
    @9
    cK
    c.le
    @11
    cW
    trlle.l
    @9
    eqid
    #
    @11
    eqid
    #
    @16
    trlle.h
    trlle.t
    trlle.r
    trlval2
    mpd3an3
    @4
    cK
    clat
    wcel
    #
    @10
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @20
    wcel
    #
    @12
    cW
    c.le
    wbr
    @0
    @19
    @1
    @3
    cK
    hllat
    ad2antrr
    #
    @4
    @19
    @7
    @20
    wcel
    #
    @8
    @20
    wcel
    #
    @21
    @23
    @4
    cK
    cops
    wcel
    #
    @22
    @24
    @0
    @26
    @1
    @3
    cK
    hlop
    ad2antrr
    @1
    @22
    @0
    @3
    @20
    cH
    cK
    cW
    @20
    eqid
    #
    trlle.h
    lhpbase
    ad2antlr
    #
    @20
    cK
    @6
    cW
    @27
    @15
    opoccl
    syl2anc
    #
    @2
    @3
    @24
    @25
    @29
    @20
    cT
    cF
    cH
    cK
    chlt
    cW
    @7
    @27
    trlle.h
    trlle.t
    ltrncl
    mpd3an3
    @20
    @9
    cK
    @7
    @8
    @27
    @17
    latjcl
    syl3anc
    @28
    @20
    cK
    c.le
    @11
    @10
    cW
    @27
    trlle.l
    @18
    latmle2
    syl3anc
    eqbrtrd
end
