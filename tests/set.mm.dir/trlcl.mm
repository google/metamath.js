include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "coc.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "catm.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "eqid.mm"
include "lhpocnel.mm"
include "adantr.mm"
include "trlval2.mm"
include "mpd3an3.mm"
include "clat.mm"
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
include "latmcl.mm"
include "eqeltrd.mm"

theorem trlcl
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  assume trlcl.b: |- B = ( Base ` K )
  assume trlcl.h: |- H = ( LHyp ` K )
  assume trlcl.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlcl.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( R ` F ) e. B )

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
    cB
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
    cK
    cple
    cfv
    #
    wbr
    wn
    wa
    #
    @5
    @12
    wceq
    @2
    @15
    @3
    @13
    cH
    cK
    @14
    @6
    cW
    @14
    eqid
    #
    @6
    eqid
    #
    @13
    eqid
    #
    trlcl.h
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
    @14
    @11
    cW
    @16
    @9
    eqid
    #
    @11
    eqid
    #
    @18
    trlcl.h
    trlcl.t
    trlcl.r
    trlval2
    mpd3an3
    @4
    cK
    clat
    wcel
    #
    @10
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @12
    cB
    wcel
    @0
    @21
    @1
    @3
    cK
    hllat
    ad2antrr
    #
    @4
    @21
    @7
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    @22
    @24
    @4
    cK
    cops
    wcel
    #
    @23
    @25
    @0
    @27
    @1
    @3
    cK
    hlop
    ad2antrr
    @1
    @23
    @0
    @3
    cB
    cH
    cK
    cW
    trlcl.b
    trlcl.h
    lhpbase
    ad2antlr
    #
    cB
    cK
    @6
    cW
    trlcl.b
    @17
    opoccl
    syl2anc
    #
    @2
    @3
    @25
    @26
    @29
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    @7
    trlcl.b
    trlcl.h
    trlcl.t
    ltrncl
    mpd3an3
    cB
    @9
    cK
    @7
    @8
    trlcl.b
    @19
    latjcl
    syl3anc
    @28
    cB
    cK
    @11
    @10
    cW
    trlcl.b
    @20
    latmcl
    syl3anc
    eqeltrd
end
