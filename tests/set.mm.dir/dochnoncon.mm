include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cin.mm"
include "csn.mm"
include "wss.mm"
include "cbs.mm"
include "eqid.mm"
include "lssss.mm"
include "dochocss.mm"
include "sylan2.mm"
include "ssrin.mm"
include "syl.mm"
include "cdih.mm"
include "ccnv.mm"
include "coc.mm"
include "cp0.mm"
include "cmee.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "crn.mm"
include "wf1o.mm"
include "clss.mm"
include "wf1.mm"
include "dihf11.mm"
include "adantr.mm"
include "f1f1orn.mm"
include "dochcl.mm"
include "dihrnlss.mm"
include "syldan.mm"
include "f1ocnvdm.mm"
include "syl2anc.mm"
include "cops.mm"
include "hlop.mm"
include "ad2antrr.mm"
include "opoccl.mm"
include "dihmeet.mm"
include "syl3anc.mm"
include "opnoncon.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "dihcnvid2.mm"
include "dochvalr.mm"
include "dochoc.mm"
include "ineq12d.mm"
include "dih0.mm"
include "3eqtr3d.mm"
include "sseqtrd.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "simpr.mm"
include "lssincl.mm"
include "lss0ss.mm"
include "eqssd.mm"

theorem dochnoncon
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dochnoncon.h: |- H = ( LHyp ` K )
  assume dochnoncon.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochnoncon.s: |- S = ( LSubSp ` U )
  assume dochnoncon.z: |- .0. = ( 0g ` U )
  assume dochnoncon.o: |- ._|_ = ( ( ocH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. S ) -> ( X i^i ( ._|_ ` X ) ) = { .0. } )

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
    cS
    wcel
    #
    wa
    #
    cX
    cX
    c.pe
    cfv
    #
    cin
    #
    c.0
    csn
    #
    @4
    @6
    @5
    c.pe
    cfv
    #
    @5
    cin
    #
    @7
    @4
    cX
    @8
    wss
    #
    @6
    @9
    wss
    @3
    @2
    cX
    cU
    cbs
    cfv
    #
    wss
    #
    @10
    cS
    cX
    @11
    cU
    @11
    eqid
    #
    dochnoncon.s
    lssss
    #
    cU
    cH
    cK
    c.pe
    @11
    cW
    cX
    dochnoncon.h
    dochnoncon.u
    @13
    dochnoncon.o
    dochocss
    sylan2
    cX
    @8
    @5
    ssrin
    syl
    @4
    @8
    cW
    cK
    cdih
    cfv
    cfv
    #
    ccnv
    cfv
    #
    @15
    cfv
    #
    @16
    cK
    coc
    cfv
    #
    cfv
    #
    @15
    cfv
    #
    cin
    #
    cK
    cp0
    cfv
    #
    @15
    cfv
    #
    @9
    @7
    @4
    @16
    @19
    cK
    cmee
    cfv
    #
    co
    #
    @15
    cfv
    #
    @21
    @23
    @4
    @2
    @16
    cK
    cbs
    cfv
    #
    wcel
    #
    @19
    @27
    wcel
    #
    @26
    @21
    wceq
    @2
    @3
    simpl
    #
    @4
    @27
    @15
    crn
    #
    @15
    wf1o
    #
    @8
    @31
    wcel
    #
    @28
    @4
    @27
    cU
    clss
    cfv
    #
    @15
    wf1
    #
    @32
    @2
    @35
    @3
    @27
    @34
    cU
    cH
    @15
    cK
    cW
    @27
    eqid
    #
    dochnoncon.h
    @15
    eqid
    #
    dochnoncon.u
    @34
    eqid
    #
    dihf11
    adantr
    @27
    @34
    @15
    f1f1orn
    syl
    @2
    @3
    @5
    @11
    wss
    #
    @33
    @4
    @5
    @34
    wcel
    #
    @39
    @2
    @3
    @5
    @31
    wcel
    #
    @40
    @3
    @2
    @12
    @41
    @14
    cU
    cH
    @15
    cK
    c.pe
    @11
    cW
    cX
    dochnoncon.h
    @37
    dochnoncon.u
    @13
    dochnoncon.o
    dochcl
    sylan2
    #
    @34
    cU
    cH
    @15
    cK
    cW
    @5
    dochnoncon.h
    dochnoncon.u
    @37
    @38
    dihrnlss
    syldan
    @34
    @5
    @11
    cU
    @13
    @38
    lssss
    syl
    cU
    cH
    @15
    cK
    c.pe
    @11
    cW
    @5
    dochnoncon.h
    @37
    dochnoncon.u
    @13
    dochnoncon.o
    dochcl
    syldan
    #
    @27
    @31
    @8
    @15
    f1ocnvdm
    syl2anc
    #
    @4
    cK
    cops
    wcel
    #
    @28
    @29
    @0
    @45
    @1
    @3
    cK
    hlop
    ad2antrr
    #
    @44
    @27
    cK
    @18
    @16
    @36
    @18
    eqid
    #
    opoccl
    syl2anc
    @27
    cH
    @15
    cK
    @24
    cW
    @16
    @19
    @36
    @24
    eqid
    #
    dochnoncon.h
    @37
    dihmeet
    syl3anc
    @4
    @25
    @22
    @15
    @4
    @45
    @28
    @25
    @22
    wceq
    @46
    @44
    @27
    cK
    @24
    @18
    @16
    @22
    @36
    @47
    @48
    @22
    eqid
    #
    opnoncon
    syl2anc
    fveq2d
    eqtr3d
    @4
    @17
    @8
    @20
    @5
    @2
    @3
    @33
    @17
    @8
    wceq
    @43
    cH
    @15
    cK
    cW
    @8
    dochnoncon.h
    @37
    dihcnvid2
    syldan
    @4
    @8
    c.pe
    cfv
    #
    @20
    @5
    @2
    @3
    @33
    @50
    @20
    wceq
    @43
    cH
    @15
    cK
    c.pe
    @18
    cW
    @8
    @47
    dochnoncon.h
    @37
    dochnoncon.o
    dochvalr
    syldan
    @2
    @3
    @41
    @50
    @5
    wceq
    @42
    cH
    @15
    cK
    c.pe
    cW
    @5
    dochnoncon.h
    @37
    dochnoncon.o
    dochoc
    syldan
    eqtr3d
    ineq12d
    @2
    @23
    @7
    wceq
    @3
    cU
    cH
    @15
    cK
    c.0
    cW
    @22
    @49
    dochnoncon.h
    @37
    dochnoncon.u
    dochnoncon.z
    dih0
    adantr
    3eqtr3d
    sseqtrd
    @4
    cU
    clmod
    wcel
    #
    @6
    cS
    wcel
    #
    @7
    @6
    wss
    @4
    cU
    cH
    cK
    cW
    dochnoncon.h
    dochnoncon.u
    @30
    dvhlmod
    #
    @4
    @51
    @3
    @5
    cS
    wcel
    #
    @52
    @53
    @2
    @3
    simpr
    @2
    @3
    @41
    @54
    @42
    cS
    cU
    cH
    @15
    cK
    cW
    @5
    dochnoncon.h
    dochnoncon.u
    @37
    dochnoncon.s
    dihrnlss
    syldan
    cS
    cX
    @5
    cU
    dochnoncon.s
    lssincl
    syl3anc
    cS
    cU
    @6
    c.0
    dochnoncon.z
    dochnoncon.s
    lss0ss
    syl2anc
    eqssd
end
