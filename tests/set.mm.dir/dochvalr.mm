include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cbs.mm"
include "crab.mm"
include "cglb.mm"
include "ccnv.mm"
include "cdvh.mm"
include "wceq.mm"
include "eqid.mm"
include "dihrnss.mm"
include "dochval.mm"
include "syldan.mm"
include "cple.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "ccla.mm"
include "hlclat.mm"
include "ssrab2.mm"
include "clatglbcl.mm"
include "sylancl.mm"
include "dihcnvcl.mm"
include "wbr.mm"
include "a1i.mm"
include "ssid.mm"
include "dihcnvid2.mm"
include "syl5sseqr.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "clatglble.mm"
include "syl3anc.mm"
include "wral.mm"
include "adantr.mm"
include "sseq1d.mm"
include "wb.mm"
include "simpll.mm"
include "simpr.mm"
include "dihord.mm"
include "bitr3d.mm"
include "biimpd.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "clatleglb.mm"
include "mpbird.mm"
include "latasymd.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem dochvalr
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let vz: setvar z
  let vy: setvar y
  assume dochvalr.o: |- ._|_ = ( oc ` K )
  assume dochvalr.h: |- H = ( LHyp ` K )
  assume dochvalr.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochvalr.n: |- N = ( ( ocH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. ran I ) -> ( N ` X ) = ( I ` ( ._|_ ` ( `' I ` X ) ) ) )

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
    wcel
    #
    wa
    #
    cX
    cN
    cfv
    #
    cX
    vy
    cv
    #
    cI
    cfv
    #
    wss
    #
    vy
    cK
    cbs
    cfv
    #
    crab
    #
    cK
    cglb
    cfv
    #
    cfv
    #
    c.pe
    cfv
    #
    cI
    cfv
    #
    cX
    cI
    ccnv
    cfv
    #
    c.pe
    cfv
    #
    cI
    cfv
    @2
    @3
    cX
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cbs
    cfv
    #
    wss
    @5
    @14
    wceq
    @17
    cH
    cI
    cK
    @18
    cW
    cX
    dochvalr.h
    @17
    eqid
    #
    dochvalr.i
    @18
    eqid
    #
    dihrnss
    vy
    @9
    @17
    @11
    cH
    cI
    cK
    cN
    c.pe
    @18
    cW
    cX
    chlt
    @9
    eqid
    #
    @11
    eqid
    #
    dochvalr.o
    dochvalr.h
    dochvalr.i
    @19
    @20
    dochvalr.n
    dochval
    syldan
    @4
    @13
    @16
    cI
    @4
    @12
    @15
    c.pe
    @4
    @9
    cK
    cK
    cple
    cfv
    #
    @12
    @15
    @21
    @23
    eqid
    #
    @0
    cK
    clat
    wcel
    @1
    @3
    cK
    hllat
    ad2antrr
    @4
    cK
    ccla
    wcel
    #
    @10
    @9
    wss
    #
    @12
    @9
    wcel
    @0
    @25
    @1
    @3
    cK
    hlclat
    ad2antrr
    #
    @8
    vy
    @9
    ssrab2
    #
    @9
    @10
    @11
    cK
    @21
    @22
    clatglbcl
    sylancl
    @9
    cH
    cI
    cK
    cW
    cX
    @21
    dochvalr.h
    dochvalr.i
    dihcnvcl
    #
    @4
    @25
    @26
    @15
    @10
    wcel
    #
    @12
    @15
    @23
    wbr
    @27
    @26
    @4
    @28
    a1i
    #
    @4
    @15
    @9
    wcel
    #
    cX
    @15
    cI
    cfv
    #
    wss
    #
    @30
    @29
    @4
    cX
    cX
    @33
    cX
    ssid
    cH
    cI
    cK
    cW
    cX
    dochvalr.h
    dochvalr.i
    dihcnvid2
    #
    syl5sseqr
    @8
    @34
    vy
    @15
    @9
    @6
    @15
    wceq
    @7
    @33
    cX
    @6
    @15
    cI
    fveq2
    sseq2d
    elrab
    sylanbrc
    @9
    @10
    @11
    cK
    @23
    @15
    @21
    @24
    @22
    clatglble
    syl3anc
    @4
    @15
    @12
    @23
    wbr
    #
    @15
    vz
    cv
    #
    @23
    wbr
    #
    vz
    @10
    wral
    #
    @4
    @38
    vz
    @10
    @37
    @10
    wcel
    @37
    @9
    wcel
    #
    cX
    @37
    cI
    cfv
    #
    wss
    #
    wa
    @4
    @38
    @8
    @42
    vy
    @37
    @9
    @6
    @37
    wceq
    @7
    @41
    cX
    @6
    @37
    cI
    fveq2
    sseq2d
    elrab
    @4
    @40
    @42
    @38
    @4
    @40
    wa
    #
    @42
    @38
    @43
    @33
    @41
    wss
    #
    @42
    @38
    @43
    @33
    cX
    @41
    @4
    @33
    cX
    wceq
    @40
    @35
    adantr
    sseq1d
    @43
    @2
    @32
    @40
    @44
    @38
    wb
    @2
    @3
    @40
    simpll
    @4
    @32
    @40
    @29
    adantr
    @4
    @40
    simpr
    @9
    cH
    cI
    cK
    @23
    cW
    @15
    @37
    @21
    @24
    dochvalr.h
    dochvalr.i
    dihord
    syl3anc
    bitr3d
    biimpd
    expimpd
    syl5bi
    ralrimiv
    @4
    @25
    @32
    @26
    @36
    @39
    wb
    @27
    @29
    @31
    vz
    @9
    @10
    @11
    cK
    @23
    @15
    @21
    @24
    @22
    clatleglb
    syl3anc
    mpbird
    latasymd
    fveq2d
    fveq2d
    eqtrd
end
