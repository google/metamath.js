include "wcel.mm"
include "wa.mm"
include "cts.mm"
include "cfv.mm"
include "ctopn.mm"
include "tngtset.mm"
include "cbs.mm"
include "cpw.mm"
include "wss.mm"
include "wceq.mm"
include "cmopn.mm"
include "cdm.mm"
include "cxmt.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "cbl.mm"
include "ctg.mm"
include "df-mopn.mm"
include "dmmptss.mm"
include "sseli.mm"
include "cxp.mm"
include "csg.mm"
include "ccom.mm"
include "cds.mm"
include "eqid.mm"
include "tngds.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "dmeqd.mm"
include "dmcoss.mm"
include "cminusg.mm"
include "cplusg.mm"
include "co.mm"
include "grpsubfval.mm"
include "ovex.mm"
include "dmmpt2.mm"
include "sseqtri.mm"
include "syl6eqssr.mm"
include "adantr.mm"
include "dmss.mm"
include "syl.mm"
include "dmxpid.mm"
include "syl6sseq.mm"
include "simpr.mm"
include "xmetunirn.mm"
include "sylib.mm"
include "mopnuni.mm"
include "tngbas.mm"
include "ad2antlr.mm"
include "3sstr3d.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "ex.mm"
include "syl5.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61d1.mm"
include "syl5eqss.mm"
include "eqsstr3d.mm"
include "topnid.mm"
include "eqtrd.mm"

theorem tngtopn
  let cD: class D
  let cT: class T
  let cG: class G
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume tngbas.t: |- T = ( G toNrmGrp N )
  assume tngtset.2: |- D = ( dist ` T )
  assume tngtset.3: |- J = ( MetOpen ` D )


  assert |- ( ( G e. V /\ N e. W ) -> J = ( TopOpen ` T ) )

  proof
    cG
    cV
    wcel
    #
    cN
    cW
    wcel
    #
    wa
    #
    cJ
    cT
    cts
    cfv
    #
    cT
    ctopn
    cfv
    #
    cD
    cT
    cG
    cJ
    cN
    cV
    cW
    tngbas.t
    tngtset.2
    tngtset.3
    tngtset
    #
    @2
    @3
    cT
    cbs
    cfv
    #
    cpw
    #
    wss
    @3
    @4
    wceq
    @2
    @3
    cJ
    @7
    @5
    @2
    cJ
    cD
    cmopn
    cfv
    #
    @7
    tngtset.3
    @2
    cD
    cmopn
    cdm
    #
    wcel
    #
    @8
    @7
    wss
    #
    @10
    cD
    cxmt
    crn
    cuni
    #
    wcel
    #
    @2
    @11
    @9
    @12
    cD
    vx
    @12
    vx
    cv
    #
    cbl
    cfv
    crn
    ctg
    cfv
    cmopn
    vx
    df-mopn
    dmmptss
    sseli
    @2
    @13
    @11
    @2
    @13
    wa
    #
    @8
    cuni
    #
    @6
    wss
    @11
    @15
    cD
    cdm
    #
    cdm
    #
    cG
    cbs
    cfv
    #
    @16
    @6
    @15
    @18
    @19
    @19
    cxp
    #
    cdm
    #
    @19
    @15
    @17
    @20
    wss
    #
    @18
    @21
    wss
    @2
    @22
    @13
    @2
    @17
    cN
    cG
    csg
    cfv
    #
    ccom
    #
    cdm
    #
    @20
    @2
    @24
    cD
    @1
    @24
    cD
    wceq
    @0
    @1
    @24
    cT
    cds
    cfv
    cD
    cT
    cG
    @23
    cN
    cW
    tngbas.t
    @23
    eqid
    #
    tngds
    tngtset.2
    syl6eqr
    adantl
    dmeqd
    @25
    @23
    cdm
    @20
    cN
    @23
    dmcoss
    vx
    vy
    @19
    @19
    @14
    vy
    cv
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    @23
    vx
    vy
    @19
    @29
    cG
    @27
    @23
    @19
    eqid
    #
    @29
    eqid
    @27
    eqid
    @26
    grpsubfval
    @14
    @28
    @29
    ovex
    dmmpt2
    sseqtri
    syl6eqssr
    adantr
    @17
    @20
    dmss
    syl
    @19
    dmxpid
    syl6sseq
    @15
    cD
    @18
    cxmt
    cfv
    wcel
    #
    @18
    @16
    wceq
    @15
    @13
    @31
    @2
    @13
    simpr
    cD
    xmetunirn
    sylib
    cD
    @8
    @18
    @8
    eqid
    mopnuni
    syl
    @1
    @19
    @6
    wceq
    @0
    @13
    @19
    cT
    cG
    cN
    cW
    tngbas.t
    @30
    tngbas
    ad2antlr
    3sstr3d
    @8
    @6
    sspwuni
    sylibr
    ex
    syl5
    @10
    wn
    @8
    c0
    @7
    cD
    cmopn
    ndmfv
    @7
    0ss
    syl6eqss
    pm2.61d1
    syl5eqss
    eqsstr3d
    @6
    @3
    cT
    @6
    eqid
    @3
    eqid
    topnid
    syl
    eqtrd
end
