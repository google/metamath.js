include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cdih.mm"
include "cfv.mm"
include "cbs.mm"
include "crab.mm"
include "cglb.mm"
include "coc.mm"
include "cple.mm"
include "wbr.mm"
include "ccla.mm"
include "simp1l.mm"
include "hlclat.mm"
include "syl.mm"
include "ssrab2.mm"
include "a1i.mm"
include "simpll3.mm"
include "simpr.mm"
include "sstrd.mm"
include "ex.mm"
include "ss2rabdv.mm"
include "eqid.mm"
include "clatglbss.mm"
include "syl3anc.mm"
include "cops.mm"
include "wb.mm"
include "hlop.mm"
include "clatglbcl.mm"
include "sylancl.mm"
include "oplecon3b.mm"
include "mpbid.mm"
include "simp1.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "dihord.mm"
include "mpbird.mm"
include "wceq.mm"
include "dochval.mm"
include "3adant3.mm"
include "simp3.mm"
include "simp2.mm"
include "3sstr4d.mm"

theorem dochss
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume dochss.h: |- H = ( LHyp ` K )
  assume dochss.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochss.v: |- V = ( Base ` U )
  assume dochss.o: |- ._|_ = ( ( ocH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ Y C_ V /\ X C_ Y ) -> ( ._|_ ` Y ) C_ ( ._|_ ` X ) )

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
    cY
    cV
    wss
    #
    cX
    cY
    wss
    #
    w3a
    #
    cY
    vz
    cv
    #
    cW
    cK
    cdih
    cfv
    cfv
    #
    cfv
    #
    wss
    #
    vz
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
    cK
    coc
    cfv
    #
    cfv
    #
    @7
    cfv
    #
    cX
    @8
    wss
    #
    vz
    @10
    crab
    #
    @12
    cfv
    #
    @14
    cfv
    #
    @7
    cfv
    #
    cY
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    @5
    @16
    @21
    wss
    #
    @15
    @20
    cK
    cple
    cfv
    #
    wbr
    #
    @5
    @19
    @13
    @25
    wbr
    #
    @26
    @5
    cK
    ccla
    wcel
    #
    @18
    @10
    wss
    #
    @11
    @18
    wss
    @27
    @5
    @0
    @28
    @0
    @1
    @3
    @4
    simp1l
    #
    cK
    hlclat
    syl
    #
    @29
    @5
    @17
    vz
    @10
    ssrab2
    #
    a1i
    @5
    @9
    @17
    vz
    @10
    @5
    @6
    @10
    wcel
    #
    wa
    #
    @9
    @17
    @34
    @9
    wa
    cX
    cY
    @8
    @2
    @3
    @4
    @33
    @9
    simpll3
    @34
    @9
    simpr
    sstrd
    ex
    ss2rabdv
    @10
    @11
    @18
    @12
    cK
    @25
    @10
    eqid
    #
    @25
    eqid
    #
    @12
    eqid
    #
    clatglbss
    syl3anc
    @5
    cK
    cops
    wcel
    #
    @19
    @10
    wcel
    #
    @13
    @10
    wcel
    #
    @27
    @26
    wb
    @5
    @0
    @38
    @30
    cK
    hlop
    syl
    #
    @5
    @28
    @29
    @39
    @31
    @32
    @10
    @18
    @12
    cK
    @35
    @37
    clatglbcl
    sylancl
    #
    @5
    @28
    @11
    @10
    wss
    @40
    @31
    @9
    vz
    @10
    ssrab2
    @10
    @11
    @12
    cK
    @35
    @37
    clatglbcl
    sylancl
    #
    @10
    cK
    @25
    @14
    @19
    @13
    @35
    @36
    @14
    eqid
    #
    oplecon3b
    syl3anc
    mpbid
    @5
    @2
    @15
    @10
    wcel
    #
    @20
    @10
    wcel
    #
    @24
    @26
    wb
    @2
    @3
    @4
    simp1
    #
    @5
    @38
    @40
    @45
    @41
    @43
    @10
    cK
    @14
    @13
    @35
    @44
    opoccl
    syl2anc
    @5
    @38
    @39
    @46
    @41
    @42
    @10
    cK
    @14
    @19
    @35
    @44
    opoccl
    syl2anc
    @10
    cH
    @7
    cK
    @25
    cW
    @15
    @20
    @35
    @36
    dochss.h
    @7
    eqid
    #
    dihord
    syl3anc
    mpbird
    @2
    @3
    @22
    @16
    wceq
    @4
    vz
    @10
    cU
    @12
    cH
    @7
    cK
    c.pe
    @14
    cV
    cW
    cY
    chlt
    @35
    @37
    @44
    dochss.h
    @48
    dochss.u
    dochss.v
    dochss.o
    dochval
    3adant3
    @5
    @2
    cX
    cV
    wss
    @23
    @21
    wceq
    @47
    @5
    cX
    cY
    cV
    @2
    @3
    @4
    simp3
    @2
    @3
    @4
    simp2
    sstrd
    vz
    @10
    cU
    @12
    cH
    @7
    cK
    c.pe
    @14
    cV
    cW
    cX
    chlt
    @35
    @37
    @44
    dochss.h
    @48
    dochss.u
    dochss.v
    dochss.o
    dochval
    syl2anc
    3sstr4d
end
