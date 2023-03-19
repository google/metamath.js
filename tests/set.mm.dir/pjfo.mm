include "cphl.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "wf.mm"
include "crn.mm"
include "wceq.mm"
include "wfo.mm"
include "pjf2.mm"
include "wss.mm"
include "frn.mm"
include "syl.mm"
include "cv.mm"
include "cocv.mm"
include "cpj1.mm"
include "co.mm"
include "eqid.mm"
include "pjval.mm"
include "ad2antlr.mm"
include "fveq1d.mm"
include "cplusg.mm"
include "clsm.mm"
include "c0g.mm"
include "ccntz.mm"
include "clss.mm"
include "csubg.mm"
include "clmod.mm"
include "phllmod.mm"
include "adantr.mm"
include "lsssssubg.mm"
include "pjdm2.mm"
include "simprbda.mm"
include "sseldd.mm"
include "lssss.mm"
include "ocvlss.mm"
include "syldan.mm"
include "cin.mm"
include "csn.mm"
include "ocvin.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablcntzd.mm"
include "pj1lid.mm"
include "eqtrd.mm"
include "wfn.mm"
include "ffn.mm"
include "sselda.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "dffo2.mm"
include "sylanbrc.mm"

theorem pjfo
  let cT: class T
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume pjf.k: |- K = ( proj ` W )
  assume pjf.v: |- V = ( Base ` W )


  assert |- ( ( W e. PreHil /\ T e. dom K ) -> ( K ` T ) : V -onto-> T )

  proof
    cW
    cphl
    wcel
    #
    cT
    cK
    cdm
    wcel
    #
    wa
    #
    cV
    cT
    cT
    cK
    cfv
    #
    wf
    #
    @3
    crn
    #
    cT
    wceq
    cV
    cT
    @3
    wfo
    cT
    cK
    cV
    cW
    pjf.k
    pjf.v
    pjf2
    #
    @2
    @5
    cT
    @2
    @4
    @5
    cT
    wss
    @6
    cV
    cT
    @3
    frn
    syl
    @2
    vx
    cT
    @5
    @2
    vx
    cv
    #
    cT
    wcel
    #
    @7
    @5
    wcel
    @2
    @8
    wa
    #
    @7
    @3
    cfv
    #
    @7
    @5
    @9
    @10
    @7
    cT
    cT
    cW
    cocv
    cfv
    #
    cfv
    #
    cW
    cpj1
    cfv
    #
    co
    #
    cfv
    @7
    @9
    @7
    @3
    @14
    @1
    @3
    @14
    wceq
    @0
    @8
    @13
    cT
    cK
    @11
    cW
    @11
    eqid
    #
    @13
    eqid
    #
    pjf.k
    pjval
    ad2antlr
    fveq1d
    @2
    @13
    cW
    cplusg
    cfv
    #
    cW
    clsm
    cfv
    #
    cT
    @12
    cW
    @7
    cW
    c0g
    cfv
    #
    cW
    ccntz
    cfv
    #
    @17
    eqid
    @18
    eqid
    #
    @19
    eqid
    #
    @20
    eqid
    #
    @2
    cW
    clss
    cfv
    #
    cW
    csubg
    cfv
    #
    cT
    @2
    cW
    clmod
    wcel
    #
    @24
    @25
    wss
    @0
    @26
    @1
    cW
    phllmod
    adantr
    #
    @24
    cW
    @24
    eqid
    #
    lsssssubg
    syl
    #
    @0
    @1
    cT
    @24
    wcel
    #
    cT
    @12
    @18
    co
    cV
    wceq
    @18
    cT
    cK
    @24
    @11
    cV
    cW
    pjf.v
    @28
    @15
    @21
    pjf.k
    pjdm2
    simprbda
    #
    sseldd
    #
    @2
    @24
    @25
    @12
    @29
    @0
    @1
    cT
    cV
    wss
    #
    @12
    @24
    wcel
    @2
    @30
    @33
    @31
    @24
    cT
    cV
    cW
    pjf.v
    @28
    lssss
    syl
    #
    cT
    @24
    @11
    cV
    cW
    pjf.v
    @15
    @28
    ocvlss
    syldan
    sseldd
    #
    @0
    @1
    @30
    cT
    @12
    cin
    @19
    csn
    wceq
    @31
    cT
    @24
    @11
    cW
    @19
    @15
    @28
    @22
    ocvin
    syldan
    @2
    cT
    @12
    cW
    @20
    @23
    @2
    @26
    cW
    cabl
    wcel
    @27
    cW
    lmodabl
    syl
    @32
    @35
    ablcntzd
    @16
    pj1lid
    eqtrd
    @9
    @3
    cV
    wfn
    #
    @7
    cV
    wcel
    @10
    @5
    wcel
    @2
    @36
    @8
    @2
    @4
    @36
    @6
    cV
    cT
    @3
    ffn
    syl
    adantr
    @2
    cT
    cV
    @7
    @34
    sselda
    cV
    @7
    @3
    fnfvelrn
    syl2anc
    eqeltrrd
    ex
    ssrdv
    eqssd
    cV
    cT
    @3
    dffo2
    sylanbrc
end
