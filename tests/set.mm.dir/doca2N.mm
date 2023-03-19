include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cfv.mm"
include "coc.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "col.mm"
include "cbs.mm"
include "wceq.mm"
include "hlol.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "diadmclN.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "oldmm1.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "clat.mm"
include "hllat.mm"
include "latmcl.mm"
include "oldmm2.mm"
include "eqtrd.mm"
include "cops.mm"
include "hlop.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "latjass.mm"
include "syl13anc.mm"
include "latjidm.mm"
include "oveq2d.mm"
include "coml.mm"
include "cple.mm"
include "wbr.mm"
include "hloml.mm"
include "latmle2.mm"
include "omlspjN.mm"
include "syl121anc.mm"
include "diadmleN.mm"
include "wb.mm"
include "latleeqm1.mm"
include "mpbid.mm"
include "3eqtrrd.mm"
include "latjcl.mm"
include "diaeldm.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "cltrn.mm"
include "diaocN.mm"
include "syldan.mm"

theorem doca2N
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  assume doca2.h: |- H = ( LHyp ` K )
  assume doca2.i: |- I = ( ( DIsoA ` K ) ` W )
  assume doca2.n: |- ._|_ = ( ( ocA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. dom I ) -> ( ._|_ ` ( ._|_ ` ( I ` X ) ) ) = ( I ` X ) )

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
    cdm
    #
    wcel
    #
    wa
    #
    cX
    cI
    cfv
    #
    cX
    cK
    coc
    cfv
    #
    cfv
    #
    cW
    @7
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
    @7
    cfv
    #
    @9
    @10
    co
    #
    cW
    @12
    co
    #
    cI
    cfv
    #
    @13
    cI
    cfv
    #
    c.pe
    cfv
    #
    @6
    c.pe
    cfv
    #
    c.pe
    cfv
    @5
    cX
    @16
    cI
    @5
    @16
    cX
    cW
    @12
    co
    #
    @9
    @10
    co
    #
    cW
    @12
    co
    #
    @21
    cX
    @5
    @15
    @22
    cW
    @12
    @5
    @15
    @22
    @9
    @10
    co
    #
    @22
    @5
    @14
    @22
    @9
    @10
    @5
    @14
    @21
    @7
    cfv
    #
    cW
    @12
    co
    #
    @7
    cfv
    #
    @22
    @5
    @13
    @26
    @7
    @5
    @26
    @13
    @5
    @25
    @11
    cW
    @12
    @5
    cK
    col
    wcel
    #
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @29
    wcel
    #
    @25
    @11
    wceq
    @0
    @28
    @1
    @4
    cK
    hlol
    ad2antrr
    #
    @29
    cH
    cI
    cK
    chlt
    cW
    cX
    @29
    eqid
    #
    doca2.h
    doca2.i
    diadmclN
    #
    @1
    @31
    @0
    @4
    @29
    cH
    cK
    cW
    @33
    doca2.h
    lhpbase
    ad2antlr
    #
    @29
    @10
    cK
    @12
    @7
    cX
    cW
    @33
    @10
    eqid
    #
    @12
    eqid
    #
    @7
    eqid
    #
    oldmm1
    syl3anc
    oveq1d
    eqcomd
    fveq2d
    @5
    @28
    @21
    @29
    wcel
    #
    @31
    @27
    @22
    wceq
    @32
    @5
    cK
    clat
    wcel
    #
    @30
    @31
    @39
    @0
    @40
    @1
    @4
    cK
    hllat
    ad2antrr
    #
    @34
    @35
    @29
    cK
    @12
    cX
    cW
    @33
    @37
    latmcl
    syl3anc
    #
    @35
    @29
    @10
    cK
    @12
    @7
    @21
    cW
    @33
    @36
    @37
    @38
    oldmm2
    syl3anc
    eqtrd
    oveq1d
    @5
    @24
    @21
    @9
    @9
    @10
    co
    #
    @10
    co
    #
    @22
    @5
    @40
    @39
    @9
    @29
    wcel
    #
    @45
    @24
    @44
    wceq
    @41
    @42
    @5
    cK
    cops
    wcel
    #
    @31
    @45
    @0
    @46
    @1
    @4
    cK
    hlop
    ad2antrr
    #
    @35
    @29
    cK
    @7
    cW
    @33
    @38
    opoccl
    syl2anc
    #
    @48
    @29
    @10
    cK
    @21
    @9
    @9
    @33
    @36
    latjass
    syl13anc
    @5
    @43
    @9
    @21
    @10
    @5
    @40
    @45
    @43
    @9
    wceq
    @41
    @48
    @29
    @10
    cK
    @9
    @33
    @36
    latjidm
    syl2anc
    oveq2d
    eqtrd
    eqtrd
    oveq1d
    @5
    cK
    coml
    wcel
    #
    @39
    @31
    @21
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @23
    @21
    wceq
    @0
    @49
    @1
    @4
    cK
    hloml
    ad2antrr
    @42
    @35
    @5
    @40
    @30
    @31
    @51
    @41
    @34
    @35
    @29
    cK
    @50
    @12
    cX
    cW
    @33
    @50
    eqid
    #
    @37
    latmle2
    syl3anc
    @29
    @10
    cK
    @50
    @12
    @7
    @21
    cW
    @33
    @52
    @36
    @37
    @38
    omlspjN
    syl121anc
    @5
    cX
    cW
    @50
    wbr
    #
    @21
    cX
    wceq
    #
    cH
    cI
    cK
    @50
    chlt
    cW
    cX
    @52
    doca2.h
    doca2.i
    diadmleN
    @5
    @40
    @30
    @31
    @53
    @54
    wb
    @41
    @34
    @35
    @29
    cK
    @50
    @12
    cX
    cW
    @33
    @52
    @37
    latleeqm1
    syl3anc
    mpbid
    3eqtrrd
    fveq2d
    @2
    @4
    @13
    @3
    wcel
    #
    @17
    @19
    wceq
    @5
    @55
    @13
    @29
    wcel
    #
    @13
    cW
    @50
    wbr
    #
    @5
    @40
    @11
    @29
    wcel
    #
    @31
    @56
    @41
    @5
    @40
    @8
    @29
    wcel
    #
    @45
    @58
    @41
    @5
    @46
    @30
    @59
    @47
    @34
    @29
    cK
    @7
    cX
    @33
    @38
    opoccl
    syl2anc
    @48
    @29
    @10
    cK
    @8
    @9
    @33
    @36
    latjcl
    syl3anc
    #
    @35
    @29
    cK
    @12
    @11
    cW
    @33
    @37
    latmcl
    syl3anc
    @5
    @40
    @58
    @31
    @57
    @41
    @60
    @35
    @29
    cK
    @50
    @12
    @11
    cW
    @33
    @52
    @37
    latmle2
    syl3anc
    @2
    @55
    @56
    @57
    wa
    wb
    @4
    @29
    cH
    cI
    cK
    @50
    chlt
    cW
    @13
    @33
    @52
    doca2.h
    doca2.i
    diaeldm
    adantr
    mpbir2and
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cH
    cI
    @10
    cK
    @12
    c.pe
    @7
    cW
    @13
    @36
    @37
    @38
    doca2.h
    @61
    eqid
    #
    doca2.i
    doca2.n
    diaocN
    syldan
    @5
    @18
    @20
    c.pe
    @61
    cH
    cI
    @10
    cK
    @12
    c.pe
    @7
    cW
    cX
    @36
    @37
    @38
    doca2.h
    @62
    doca2.i
    doca2.n
    diaocN
    fveq2d
    3eqtrrd
end
