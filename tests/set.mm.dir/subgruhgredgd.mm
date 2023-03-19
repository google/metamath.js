include "cvtx.mm"
include "cfv.mm"
include "wss.mm"
include "ciedg.mm"
include "cedg.mm"
include "cpw.mm"
include "w3a.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "csubgr.mm"
include "wbr.mm"
include "eqid.mm"
include "subgrprop2.mm"
include "syl.mm"
include "wa.mm"
include "wne.mm"
include "simpr3.mm"
include "crn.mm"
include "wfun.mm"
include "cdm.mm"
include "cuhgr.mm"
include "subgruhgrfun.mm"
include "syl2anc.mm"
include "dmeqi.mm"
include "syl6eleq.mm"
include "jca.mm"
include "adantr.mm"
include "fveq1i.mm"
include "fvelrn.mm"
include "syl5eqel.mm"
include "edgval.mm"
include "syl6eleqr.mm"
include "sseldd.mm"
include "wceq.mm"
include "uhgrfun.mm"
include "simpr2.mm"
include "funssfv.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "wfn.mm"
include "funfn.mm"
include "sylib.mm"
include "subgreldmiedg.mm"
include "uhgrn0.mm"
include "eqnetrd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "mpdan.mm"

theorem subgruhgredgd
  let wph: wff ph
  let cS: class S
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  assume subgruhgredgd.v: |- V = ( Vtx ` S )
  assume subgruhgredgd.i: |- I = ( iEdg ` S )
  assume subgruhgredgd.g: |- ( ph -> G e. UHGraph )
  assume subgruhgredgd.s: |- ( ph -> S SubGraph G )
  assume subgruhgredgd.x: |- ( ph -> X e. dom I )


  assert |- ( ph -> ( I ` X ) e. ( ~P V \ { (/) } ) )

  proof
    wph
    cV
    cG
    cvtx
    cfv
    #
    wss
    #
    cI
    cG
    ciedg
    cfv
    #
    wss
    #
    cS
    cedg
    cfv
    #
    cV
    cpw
    #
    wss
    #
    w3a
    #
    cX
    cI
    cfv
    #
    @5
    c0
    csn
    cdif
    wcel
    #
    wph
    cS
    cG
    csubgr
    wbr
    #
    @7
    subgruhgredgd.s
    @0
    @2
    cS
    @4
    cG
    cI
    cV
    subgruhgredgd.v
    @0
    eqid
    subgruhgredgd.i
    @2
    eqid
    #
    @4
    eqid
    subgrprop2
    syl
    wph
    @7
    wa
    #
    @8
    @5
    wcel
    @8
    c0
    wne
    @9
    @12
    @4
    @5
    @8
    wph
    @1
    @3
    @6
    simpr3
    @12
    @8
    cS
    ciedg
    cfv
    #
    crn
    #
    @4
    @12
    @13
    wfun
    #
    cX
    @13
    cdm
    #
    wcel
    #
    wa
    #
    @8
    @14
    wcel
    wph
    @18
    @7
    wph
    @15
    @17
    wph
    cG
    cuhgr
    wcel
    #
    @10
    @15
    subgruhgredgd.g
    subgruhgredgd.s
    cS
    cG
    subgruhgrfun
    syl2anc
    wph
    cX
    cI
    cdm
    #
    @16
    subgruhgredgd.x
    cI
    @13
    subgruhgredgd.i
    dmeqi
    syl6eleq
    #
    jca
    adantr
    @18
    @8
    cX
    @13
    cfv
    @14
    cX
    cI
    @13
    subgruhgredgd.i
    fveq1i
    cX
    @13
    fvelrn
    syl5eqel
    syl
    cS
    edgval
    syl6eleqr
    sseldd
    @12
    @8
    cX
    @2
    cfv
    #
    c0
    @12
    @2
    wfun
    #
    @3
    cX
    @20
    wcel
    #
    @8
    @22
    wceq
    wph
    @23
    @7
    wph
    @19
    @23
    subgruhgredgd.g
    @2
    cG
    @11
    uhgrfun
    syl
    #
    adantr
    wph
    @1
    @3
    @6
    simpr2
    wph
    @24
    @7
    subgruhgredgd.x
    adantr
    @23
    @3
    @24
    w3a
    @22
    @8
    cX
    @2
    cI
    funssfv
    eqcomd
    syl3anc
    @12
    @19
    @2
    @2
    cdm
    #
    wfn
    #
    cX
    @26
    wcel
    #
    @22
    c0
    wne
    wph
    @19
    @7
    subgruhgredgd.g
    adantr
    wph
    @27
    @7
    wph
    @23
    @27
    @25
    @2
    funfn
    sylib
    adantr
    wph
    @28
    @7
    wph
    @10
    @17
    @28
    subgruhgredgd.s
    @21
    cS
    cG
    cX
    subgreldmiedg
    syl2anc
    adantr
    @26
    @2
    cX
    cG
    @11
    uhgrn0
    syl3anc
    eqnetrd
    @8
    @5
    c0
    eldifsn
    sylanbrc
    mpdan
end
