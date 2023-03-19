include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "c0.mm"
include "cres.mm"
include "c1o.mm"
include "cfv.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "cop.mm"
include "cvv.mm"
include "wcel.mm"
include "csubg.mm"
include "0ex.mm"
include "dprdsn.mm"
include "sylancr.mm"
include "simpld.mm"
include "c2o.mm"
include "wfn.mm"
include "wf.mm"
include "xpscf.mm"
include "sylanbrc.mm"
include "ffn.mm"
include "syl.mm"
include "cpr.mm"
include "prid1.mm"
include "df2o3.mm"
include "eleqtrri.mm"
include "fnressn.mm"
include "sylancl.mm"
include "xpsc0.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "prid2.mm"
include "xpsc1.mm"
include "w3a.mm"
include "wne.mm"
include "1n0.mm"
include "necomi.mm"
include "disjsn2.mm"
include "mp1i.mm"
include "cun.mm"
include "df-pr.mm"
include "eqtri.mm"
include "a1i.mm"
include "dmdprdsplit.mm"
include "3anass.mm"
include "syl6bb.mm"
include "baibd.mm"
include "ex.mm"
include "mp2and.mm"
include "oveq2d.mm"
include "simprd.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "ineq12d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem dmdprdpr
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cG: class G
  let c.0: class .0.
  let cZ: class Z
  assume dmdprdpr.z: |- Z = ( Cntz ` G )
  assume dmdprdpr.0: |- .0. = ( 0g ` G )
  assume dmdprdpr.s: |- ( ph -> S e. ( SubGrp ` G ) )
  assume dmdprdpr.t: |- ( ph -> T e. ( SubGrp ` G ) )


  assert |- ( ph -> ( G dom DProd `' ( { S } +c { T } ) <-> ( S C_ ( Z ` T ) /\ ( S i^i T ) = { .0. } ) ) )

  proof
    wph
    cG
    cS
    csn
    cT
    csn
    ccda
    co
    ccnv
    #
    cdprd
    cdm
    #
    wbr
    #
    cG
    @0
    c0
    csn
    #
    cres
    #
    cdprd
    co
    #
    cG
    @0
    c1o
    csn
    #
    cres
    #
    cdprd
    co
    #
    cZ
    cfv
    #
    wss
    #
    @5
    @8
    cin
    #
    c.0
    csn
    #
    wceq
    #
    wa
    #
    cS
    cT
    cZ
    cfv
    #
    wss
    #
    cS
    cT
    cin
    #
    @12
    wceq
    #
    wa
    wph
    cG
    @4
    @1
    wbr
    #
    cG
    @7
    @1
    wbr
    #
    @2
    @14
    wb
    #
    wph
    cG
    c0
    cS
    cop
    #
    csn
    #
    @4
    @1
    wph
    cG
    @23
    @1
    wbr
    #
    cG
    @23
    cdprd
    co
    #
    cS
    wceq
    #
    wph
    c0
    cvv
    wcel
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    @24
    @26
    wa
    0ex
    dmdprdpr.s
    c0
    cS
    cG
    cvv
    dprdsn
    sylancr
    #
    simpld
    wph
    @4
    c0
    c0
    @0
    cfv
    #
    cop
    #
    csn
    #
    @23
    wph
    @0
    c2o
    wfn
    #
    c0
    c2o
    wcel
    @4
    @32
    wceq
    wph
    c2o
    @27
    @0
    wf
    #
    @33
    wph
    @28
    cT
    @27
    wcel
    #
    @34
    dmdprdpr.s
    dmdprdpr.t
    @27
    cS
    cT
    xpscf
    sylanbrc
    #
    c2o
    @27
    @0
    ffn
    syl
    #
    c0
    c0
    c1o
    cpr
    #
    c2o
    c0
    c1o
    0ex
    prid1
    df2o3
    eleqtrri
    c2o
    c0
    @0
    fnressn
    sylancl
    wph
    @31
    @22
    wph
    @30
    cS
    c0
    wph
    @28
    @30
    cS
    wceq
    dmdprdpr.s
    cS
    cT
    @27
    xpsc0
    syl
    opeq2d
    sneqd
    eqtrd
    #
    breqtrrd
    wph
    cG
    c1o
    cT
    cop
    #
    csn
    #
    @7
    @1
    wph
    cG
    @41
    @1
    wbr
    #
    cG
    @41
    cdprd
    co
    #
    cT
    wceq
    #
    wph
    c1o
    con0
    wcel
    @35
    @42
    @44
    wa
    1on
    dmdprdpr.t
    c1o
    cT
    cG
    con0
    dprdsn
    sylancr
    #
    simpld
    wph
    @7
    c1o
    c1o
    @0
    cfv
    #
    cop
    #
    csn
    #
    @41
    wph
    @33
    c1o
    c2o
    wcel
    @7
    @48
    wceq
    @37
    c1o
    @38
    c2o
    c0
    c1o
    c1o
    con0
    1on
    elexi
    prid2
    df2o3
    eleqtrri
    c2o
    c1o
    @0
    fnressn
    sylancl
    wph
    @47
    @40
    wph
    @46
    cT
    c1o
    wph
    @35
    @46
    cT
    wceq
    dmdprdpr.t
    cS
    cT
    @27
    xpsc1
    syl
    opeq2d
    sneqd
    eqtrd
    #
    breqtrrd
    wph
    @19
    @20
    wa
    #
    @21
    wph
    @2
    @50
    @14
    wph
    @2
    @50
    @10
    @13
    w3a
    @50
    @14
    wa
    wph
    @3
    @6
    @0
    cG
    c2o
    c.0
    cZ
    @36
    c0
    c1o
    wne
    @3
    @6
    cin
    c0
    wceq
    wph
    c1o
    c0
    1n0
    necomi
    c0
    c1o
    disjsn2
    mp1i
    c2o
    @3
    @6
    cun
    #
    wceq
    wph
    c2o
    @38
    @51
    df2o3
    c0
    c1o
    df-pr
    eqtri
    a1i
    dmdprdpr.z
    dmdprdpr.0
    dmdprdsplit
    @50
    @10
    @13
    3anass
    syl6bb
    baibd
    ex
    mp2and
    wph
    @10
    @16
    @13
    @18
    wph
    @5
    cS
    @9
    @15
    wph
    @5
    @25
    cS
    wph
    @4
    @23
    cG
    cdprd
    @39
    oveq2d
    wph
    @24
    @26
    @29
    simprd
    eqtrd
    #
    wph
    @8
    cT
    cZ
    wph
    @8
    @43
    cT
    wph
    @7
    @41
    cG
    cdprd
    @49
    oveq2d
    wph
    @42
    @44
    @45
    simprd
    eqtrd
    #
    fveq2d
    sseq12d
    wph
    @11
    @17
    @12
    wph
    @5
    cS
    @8
    cT
    @52
    @53
    ineq12d
    eqeq1d
    anbi12d
    bitrd
end
