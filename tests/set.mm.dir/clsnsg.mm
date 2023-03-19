include "ctgp.mm"
include "wcel.mm"
include "cnsg.mm"
include "cfv.mm"
include "wa.mm"
include "ccl.mm"
include "csubg.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "csg.mm"
include "wral.mm"
include "cbs.mm"
include "nsgsubg.mm"
include "clssubg.mm"
include "sylan2.mm"
include "cmpt.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "cima.mm"
include "cres.mm"
include "df-ima.mm"
include "cuni.mm"
include "ctop.mm"
include "ctopon.mm"
include "eqid.mm"
include "tgptopon.mm"
include "ad2antrr.mm"
include "topontop.mm"
include "syl.mm"
include "ad2antlr.mm"
include "subgss.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "clsss3.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"
include "resmptd.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "ccn.mm"
include "ctmd.mm"
include "tgptmd.mm"
include "simpr.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "cnmpt1plusg.mm"
include "ctx.mm"
include "tgpsubcn.mm"
include "cnmpt12f.mm"
include "cnclsi.mm"
include "nsgconj.mm"
include "3expa.mm"
include "adantlll.mm"
include "fmptd.mm"
include "frn.mm"
include "eqsstrd.mm"
include "clsss.mm"
include "syl3anc.mm"
include "sstrd.mm"
include "eqsstr3d.mm"
include "wfn.mm"
include "ovex.mm"
include "fnmpti.mm"
include "df-f.mm"
include "mpbiran.mm"
include "sylibr.mm"
include "fmpt.mm"
include "ralrimiva.mm"
include "isnsg3.mm"
include "sylanbrc.mm"

theorem clsnsg
  let cS: class S
  let cG: class G
  let cJ: class J
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cR: class R
  let cX: class X
  assume subgntr.h: |- J = ( TopOpen ` G )


  assert |- ( ( G e. TopGrp /\ S e. ( NrmSGrp ` G ) ) -> ( ( cls ` J ) ` S ) e. ( NrmSGrp ` G ) )

  proof
    cG
    ctgp
    wcel
    #
    cS
    cG
    cnsg
    cfv
    #
    wcel
    #
    wa
    #
    cS
    cJ
    ccl
    cfv
    #
    cfv
    #
    cG
    csubg
    cfv
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @8
    cG
    csg
    cfv
    #
    co
    #
    @5
    wcel
    vy
    @5
    wral
    #
    vx
    cG
    cbs
    cfv
    #
    wral
    @5
    @1
    wcel
    @2
    @0
    cS
    @6
    wcel
    #
    @7
    cS
    cG
    nsgsubg
    #
    cS
    cG
    cJ
    subgntr.h
    clssubg
    sylan2
    @3
    @14
    vx
    @15
    @3
    @8
    @15
    wcel
    #
    wa
    #
    @5
    @5
    vy
    @5
    @13
    cmpt
    #
    wf
    #
    @14
    @19
    @20
    crn
    #
    @5
    wss
    #
    @21
    @19
    @22
    vy
    @15
    @13
    cmpt
    #
    @5
    cima
    #
    @5
    @19
    @25
    @24
    @5
    cres
    #
    crn
    @22
    @24
    @5
    df-ima
    @19
    @26
    @20
    @19
    vy
    @15
    @5
    @13
    @19
    @5
    cJ
    cuni
    #
    @15
    @19
    cJ
    ctop
    wcel
    #
    cS
    @27
    wss
    #
    @5
    @27
    wss
    @19
    cJ
    @15
    ctopon
    cfv
    wcel
    #
    @28
    @0
    @30
    @2
    @18
    cG
    cJ
    @15
    subgntr.h
    @15
    eqid
    #
    tgptopon
    ad2antrr
    #
    @15
    cJ
    topontop
    syl
    #
    @19
    cS
    @15
    @27
    @19
    @16
    cS
    @15
    wss
    @2
    @16
    @0
    @18
    @17
    ad2antlr
    @15
    cS
    cG
    @31
    subgss
    syl
    #
    @19
    @30
    @15
    @27
    wceq
    @32
    @15
    cJ
    toponuni
    syl
    #
    sseqtrd
    #
    cS
    cJ
    @27
    @27
    eqid
    #
    clsss3
    syl2anc
    @35
    sseqtr4d
    resmptd
    rneqd
    syl5eq
    @19
    @25
    @24
    cS
    cima
    #
    @4
    cfv
    #
    @5
    @19
    @24
    cJ
    cJ
    ccn
    co
    wcel
    @29
    @25
    @39
    wss
    @19
    vy
    @11
    @8
    @12
    cJ
    cJ
    cJ
    cJ
    @15
    @32
    @19
    vy
    @8
    @9
    @10
    cG
    cJ
    cJ
    @15
    subgntr.h
    @10
    eqid
    #
    @0
    cG
    ctmd
    wcel
    @2
    @18
    cG
    tgptmd
    ad2antrr
    @32
    @19
    vy
    @8
    cJ
    cJ
    @15
    @15
    @32
    @32
    @3
    @18
    simpr
    cnmptc
    #
    @19
    vy
    cJ
    @15
    @32
    cnmptid
    cnmpt1plusg
    @41
    @0
    @12
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    @2
    @18
    cG
    cJ
    @12
    subgntr.h
    @12
    eqid
    #
    tgpsubcn
    ad2antrr
    cnmpt12f
    @36
    cS
    @24
    cJ
    cJ
    @27
    @37
    cnclsi
    syl2anc
    @19
    @28
    @29
    @38
    cS
    wss
    @39
    @5
    wss
    @33
    @36
    @19
    @38
    vy
    cS
    @13
    cmpt
    #
    crn
    #
    cS
    @19
    @38
    @24
    cS
    cres
    #
    crn
    @44
    @24
    cS
    df-ima
    @19
    @45
    @43
    @19
    vy
    @15
    cS
    @13
    @34
    resmptd
    rneqd
    syl5eq
    @19
    cS
    cS
    @43
    wf
    @44
    cS
    wss
    @19
    vy
    cS
    @13
    cS
    @43
    @2
    @18
    @9
    cS
    wcel
    #
    @13
    cS
    wcel
    #
    @0
    @2
    @18
    @46
    @47
    @8
    @9
    @10
    cS
    cG
    @12
    @15
    @31
    @40
    @42
    nsgconj
    3expa
    adantlll
    @43
    eqid
    fmptd
    cS
    cS
    @43
    frn
    syl
    eqsstrd
    cS
    @38
    cJ
    @27
    @37
    clsss
    syl3anc
    sstrd
    eqsstr3d
    @21
    @20
    @5
    wfn
    @23
    vy
    @5
    @13
    @20
    @11
    @8
    @12
    ovex
    @20
    eqid
    #
    fnmpti
    @5
    @5
    @20
    df-f
    mpbiran
    sylibr
    vy
    @5
    @5
    @13
    @20
    @48
    fmpt
    sylibr
    ralrimiva
    vx
    vy
    @10
    @5
    cG
    @12
    @15
    @31
    @40
    @42
    isnsg3
    sylanbrc
end
