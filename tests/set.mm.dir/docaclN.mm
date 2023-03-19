include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "cv.mm"
include "crn.mm"
include "crab.mm"
include "cint.mm"
include "ccnv.mm"
include "coc.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "eqid.mm"
include "docavalN.mm"
include "wfun.mm"
include "cdm.mm"
include "wf1o.mm"
include "diaf11N.mm"
include "f1ofun.mm"
include "syl.mm"
include "adantr.mm"
include "cbs.mm"
include "cple.mm"
include "wbr.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "cops.mm"
include "hlop.mm"
include "c0.mm"
include "wne.mm"
include "simpl.mm"
include "ssrab2.mm"
include "a1i.mm"
include "dia1elN.mm"
include "anim1i.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylibr.mm"
include "ne0i.mm"
include "diaintclN.mm"
include "syl12anc.mm"
include "diacnvclN.mm"
include "syldan.mm"
include "diadmclN.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "latmcl.mm"
include "latmle2.mm"
include "wb.mm"
include "diaeldm.mm"
include "mpbir2and.mm"
include "fvelrn.mm"
include "eqeltrd.mm"

theorem docaclN
  let cT: class T
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let vz: setvar z
  assume docacl.h: |- H = ( LHyp ` K )
  assume docacl.t: |- T = ( ( LTrn ` K ) ` W )
  assume docacl.i: |- I = ( ( DIsoA ` K ) ` W )
  assume docacl.n: |- ._|_ = ( ( ocA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X C_ T ) -> ( ._|_ ` X ) e. ran I )

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
    cT
    wss
    #
    wa
    #
    cX
    c.pe
    cfv
    cX
    vz
    cv
    #
    wss
    #
    vz
    cI
    crn
    #
    crab
    #
    cint
    #
    cI
    ccnv
    cfv
    #
    cK
    coc
    cfv
    #
    cfv
    #
    cW
    @11
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
    cI
    cfv
    #
    @7
    vz
    cT
    cH
    cI
    @14
    cK
    @16
    c.pe
    @11
    cW
    cX
    @14
    eqid
    #
    @16
    eqid
    #
    @11
    eqid
    #
    docacl.h
    docacl.t
    docacl.i
    docacl.n
    docavalN
    @4
    cI
    wfun
    #
    @17
    cI
    cdm
    #
    wcel
    #
    @18
    @7
    wcel
    @2
    @22
    @3
    @2
    @23
    @7
    cI
    wf1o
    @22
    cH
    cI
    cK
    cW
    docacl.h
    docacl.i
    diaf11N
    @23
    @7
    cI
    f1ofun
    syl
    adantr
    @4
    @24
    @17
    cK
    cbs
    cfv
    #
    wcel
    #
    @17
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @4
    cK
    clat
    wcel
    #
    @15
    @25
    wcel
    #
    cW
    @25
    wcel
    #
    @26
    @0
    @29
    @1
    @3
    cK
    hllat
    ad2antrr
    #
    @4
    @29
    @12
    @25
    wcel
    #
    @13
    @25
    wcel
    #
    @30
    @32
    @4
    cK
    cops
    wcel
    #
    @10
    @25
    wcel
    #
    @33
    @0
    @35
    @1
    @3
    cK
    hlop
    ad2antrr
    #
    @2
    @3
    @10
    @23
    wcel
    #
    @36
    @2
    @3
    @9
    @7
    wcel
    #
    @38
    @4
    @2
    @8
    @7
    wss
    #
    @8
    c0
    wne
    #
    @39
    @2
    @3
    simpl
    @40
    @4
    @6
    vz
    @7
    ssrab2
    a1i
    @4
    cT
    @8
    wcel
    #
    @41
    @4
    cT
    @7
    wcel
    #
    @3
    wa
    @42
    @2
    @43
    @3
    cT
    cH
    cI
    cK
    cW
    docacl.h
    docacl.t
    docacl.i
    dia1elN
    anim1i
    @6
    @3
    vz
    cT
    @7
    @5
    cT
    cX
    sseq2
    elrab
    sylibr
    @8
    cT
    ne0i
    syl
    @8
    cH
    cI
    cK
    cW
    docacl.h
    docacl.i
    diaintclN
    syl12anc
    cH
    cI
    cK
    cW
    @9
    docacl.h
    docacl.i
    diacnvclN
    syldan
    @25
    cH
    cI
    cK
    chlt
    cW
    @10
    @25
    eqid
    #
    docacl.h
    docacl.i
    diadmclN
    syldan
    @25
    cK
    @11
    @10
    @44
    @21
    opoccl
    syl2anc
    @4
    @35
    @31
    @34
    @37
    @1
    @31
    @0
    @3
    @25
    cH
    cK
    cW
    @44
    docacl.h
    lhpbase
    ad2antlr
    #
    @25
    cK
    @11
    cW
    @44
    @21
    opoccl
    syl2anc
    @25
    @14
    cK
    @12
    @13
    @44
    @19
    latjcl
    syl3anc
    #
    @45
    @25
    cK
    @16
    @15
    cW
    @44
    @20
    latmcl
    syl3anc
    @4
    @29
    @30
    @31
    @28
    @32
    @46
    @45
    @25
    cK
    @27
    @16
    @15
    cW
    @44
    @27
    eqid
    #
    @20
    latmle2
    syl3anc
    @2
    @24
    @26
    @28
    wa
    wb
    @3
    @25
    cH
    cI
    cK
    @27
    chlt
    cW
    @17
    @44
    @47
    docacl.h
    docacl.i
    diaeldm
    adantr
    mpbir2and
    @17
    cI
    fvelrn
    syl2anc
    eqeltrd
end
