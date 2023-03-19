include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "cdih.mm"
include "cfv.mm"
include "crn.mm"
include "crab.mm"
include "cint.mm"
include "ssintub.mm"
include "ccnv.mm"
include "coc.mm"
include "wceq.mm"
include "eqid.mm"
include "dochcl.mm"
include "dochvalr.mm"
include "syldan.mm"
include "dochval2.mm"
include "fveq2d.mm"
include "cbs.mm"
include "wf1o.mm"
include "clss.mm"
include "wf1.mm"
include "dihf11.mm"
include "adantr.mm"
include "f1f1orn.mm"
include "syl.mm"
include "cops.mm"
include "hlop.mm"
include "ad2antrr.mm"
include "c0.mm"
include "wne.mm"
include "simpl.mm"
include "ssrab2.mm"
include "a1i.mm"
include "cp1.mm"
include "dih1.mm"
include "wfn.mm"
include "f1fn.mm"
include "op1cl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "simpr.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "dihintcl.mm"
include "syl12anc.mm"
include "f1ocnvdm.mm"
include "opoccl.mm"
include "f1ocnvfv1.mm"
include "eqtrd.mm"
include "opococ.mm"
include "f1ocnvfv2.mm"
include "3eqtrrd.mm"
include "syl5sseq.mm"

theorem dochocss
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let vz: setvar z
  let cY: class Y
  assume dochss.h: |- H = ( LHyp ` K )
  assume dochss.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochss.v: |- V = ( Base ` U )
  assume dochss.o: |- ._|_ = ( ( ocH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X C_ V ) -> X C_ ( ._|_ ` ( ._|_ ` X ) ) )

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
    cV
    wss
    #
    wa
    #
    cX
    vz
    cv
    #
    wss
    #
    vz
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    #
    crab
    #
    cint
    #
    cX
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    vz
    cX
    @8
    ssintub
    @4
    @12
    @11
    @7
    ccnv
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
    @10
    @13
    cfv
    #
    @7
    cfv
    #
    @10
    @2
    @3
    @11
    @8
    wcel
    @12
    @17
    wceq
    cU
    cH
    @7
    cK
    c.pe
    cV
    cW
    cX
    dochss.h
    @7
    eqid
    #
    dochss.u
    dochss.v
    dochss.o
    dochcl
    cH
    @7
    cK
    c.pe
    @15
    cW
    @11
    @15
    eqid
    #
    dochss.h
    @20
    dochss.o
    dochvalr
    syldan
    @4
    @16
    @18
    @7
    @4
    @16
    @18
    @15
    cfv
    #
    @15
    cfv
    #
    @18
    @4
    @14
    @22
    @15
    @4
    @14
    @22
    @7
    cfv
    #
    @13
    cfv
    #
    @22
    @4
    @11
    @24
    @13
    vz
    cU
    cH
    @7
    cK
    c.pe
    @15
    cV
    cW
    cX
    @21
    dochss.h
    @20
    dochss.u
    dochss.v
    dochss.o
    dochval2
    fveq2d
    @4
    cK
    cbs
    cfv
    #
    @8
    @7
    wf1o
    #
    @22
    @26
    wcel
    #
    @25
    @22
    wceq
    @4
    @26
    cU
    clss
    cfv
    #
    @7
    wf1
    #
    @27
    @2
    @30
    @3
    @26
    @29
    cU
    cH
    @7
    cK
    cW
    @26
    eqid
    #
    dochss.h
    @20
    dochss.u
    @29
    eqid
    dihf11
    adantr
    #
    @26
    @29
    @7
    f1f1orn
    syl
    #
    @4
    cK
    cops
    wcel
    #
    @18
    @26
    wcel
    #
    @28
    @0
    @34
    @1
    @3
    cK
    hlop
    ad2antrr
    #
    @4
    @27
    @10
    @8
    wcel
    #
    @35
    @33
    @4
    @2
    @9
    @8
    wss
    #
    @9
    c0
    wne
    #
    @37
    @2
    @3
    simpl
    @38
    @4
    @6
    vz
    @8
    ssrab2
    a1i
    @4
    cV
    @9
    wcel
    #
    @39
    @4
    cV
    @8
    wcel
    @3
    @40
    @4
    cK
    cp1
    cfv
    #
    @7
    cfv
    #
    cV
    @8
    @2
    @42
    cV
    wceq
    @3
    cU
    @41
    cH
    @7
    cK
    cV
    cW
    @41
    eqid
    #
    dochss.h
    @20
    dochss.u
    dochss.v
    dih1
    adantr
    @4
    @7
    @26
    wfn
    #
    @41
    @26
    wcel
    #
    @42
    @8
    wcel
    @4
    @30
    @44
    @32
    @26
    @29
    @7
    f1fn
    syl
    @4
    @34
    @45
    @36
    @26
    @41
    cK
    @31
    @43
    op1cl
    syl
    @26
    @41
    @7
    fnfvelrn
    syl2anc
    eqeltrrd
    @2
    @3
    simpr
    @6
    @3
    vz
    cV
    @8
    @5
    cV
    cX
    sseq2
    elrab
    sylanbrc
    @9
    cV
    ne0i
    syl
    @9
    cH
    @7
    cK
    cW
    dochss.h
    @20
    dihintcl
    syl12anc
    #
    @26
    @8
    @10
    @7
    f1ocnvdm
    syl2anc
    #
    @26
    cK
    @15
    @18
    @31
    @21
    opoccl
    syl2anc
    @26
    @8
    @22
    @7
    f1ocnvfv1
    syl2anc
    eqtrd
    fveq2d
    @4
    @34
    @35
    @23
    @18
    wceq
    @36
    @47
    @26
    cK
    @15
    @18
    @31
    @21
    opococ
    syl2anc
    eqtrd
    fveq2d
    @4
    @27
    @37
    @19
    @10
    wceq
    @33
    @46
    @26
    @8
    @10
    @7
    f1ocnvfv2
    syl2anc
    3eqtrrd
    syl5sseq
end
