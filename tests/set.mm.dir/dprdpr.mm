include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cdprd.mm"
include "c0.mm"
include "cres.mm"
include "c1o.mm"
include "c2o.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wf.mm"
include "xpscf.mm"
include "sylanbrc.mm"
include "wne.mm"
include "cin.mm"
include "wceq.mm"
include "1n0.mm"
include "necomi.mm"
include "disjsn2.mm"
include "mp1i.mm"
include "cun.mm"
include "cpr.mm"
include "df2o3.mm"
include "df-pr.mm"
include "eqtri.mm"
include "a1i.mm"
include "cdm.mm"
include "wbr.mm"
include "wss.mm"
include "dmdprdpr.mm"
include "mpbir2and.mm"
include "dprdsplit.mm"
include "cop.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "0ex.mm"
include "prid1.mm"
include "eleqtrri.mm"
include "fnressn.mm"
include "sylancl.mm"
include "xpsc0.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cvv.mm"
include "wa.mm"
include "dprdsn.mm"
include "sylancr.mm"
include "simprd.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "prid2.mm"
include "xpsc1.mm"
include "oveq12d.mm"

theorem dprdpr
  let wph: wff ph
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cG: class G
  let c.0: class .0.
  let cZ: class Z
  assume dmdprdpr.z: |- Z = ( Cntz ` G )
  assume dmdprdpr.0: |- .0. = ( 0g ` G )
  assume dmdprdpr.s: |- ( ph -> S e. ( SubGrp ` G ) )
  assume dmdprdpr.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume dprdpr.s: |- .(+) = ( LSSum ` G )
  assume dprdpr.1: |- ( ph -> S C_ ( Z ` T ) )
  assume dprdpr.2: |- ( ph -> ( S i^i T ) = { .0. } )


  assert |- ( ph -> ( G DProd `' ( { S } +c { T } ) ) = ( S .(+) T ) )

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
    co
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
    c.po
    co
    cS
    cT
    c.po
    co
    wph
    @1
    @4
    c.po
    @0
    cG
    c2o
    wph
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cT
    @7
    wcel
    #
    c2o
    @7
    @0
    wf
    #
    dmdprdpr.s
    dmdprdpr.t
    @7
    cS
    cT
    xpscf
    sylanbrc
    #
    c0
    c1o
    wne
    @1
    @4
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
    @1
    @4
    cun
    #
    wceq
    wph
    c2o
    c0
    c1o
    cpr
    #
    @12
    df2o3
    c0
    c1o
    df-pr
    eqtri
    a1i
    dprdpr.s
    wph
    cG
    @0
    cdprd
    cdm
    #
    wbr
    cS
    cT
    cZ
    cfv
    wss
    cS
    cT
    cin
    c.0
    csn
    wceq
    dprdpr.1
    dprdpr.2
    wph
    cS
    cT
    cG
    c.0
    cZ
    dmdprdpr.z
    dmdprdpr.0
    dmdprdpr.s
    dmdprdpr.t
    dmdprdpr
    mpbir2and
    dprdsplit
    wph
    @3
    cS
    @6
    cT
    c.po
    wph
    @3
    cG
    c0
    cS
    cop
    #
    csn
    #
    cdprd
    co
    #
    cS
    wph
    @2
    @16
    cG
    cdprd
    wph
    @2
    c0
    c0
    @0
    cfv
    #
    cop
    #
    csn
    #
    @16
    wph
    @0
    c2o
    wfn
    #
    c0
    c2o
    wcel
    @2
    @20
    wceq
    wph
    @10
    @21
    @11
    c2o
    @7
    @0
    ffn
    syl
    #
    c0
    @13
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
    @19
    @15
    wph
    @18
    cS
    c0
    wph
    @8
    @18
    cS
    wceq
    dmdprdpr.s
    cS
    cT
    @7
    xpsc0
    syl
    opeq2d
    sneqd
    eqtrd
    oveq2d
    wph
    cG
    @16
    @14
    wbr
    #
    @17
    cS
    wceq
    #
    wph
    c0
    cvv
    wcel
    @8
    @23
    @24
    wa
    0ex
    dmdprdpr.s
    c0
    cS
    cG
    cvv
    dprdsn
    sylancr
    simprd
    eqtrd
    wph
    @6
    cG
    c1o
    cT
    cop
    #
    csn
    #
    cdprd
    co
    #
    cT
    wph
    @5
    @26
    cG
    cdprd
    wph
    @5
    c1o
    c1o
    @0
    cfv
    #
    cop
    #
    csn
    #
    @26
    wph
    @21
    c1o
    c2o
    wcel
    @5
    @30
    wceq
    @22
    c1o
    @13
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
    @29
    @25
    wph
    @28
    cT
    c1o
    wph
    @9
    @28
    cT
    wceq
    dmdprdpr.t
    cS
    cT
    @7
    xpsc1
    syl
    opeq2d
    sneqd
    eqtrd
    oveq2d
    wph
    cG
    @26
    @14
    wbr
    #
    @27
    cT
    wceq
    #
    wph
    c1o
    con0
    wcel
    @9
    @31
    @32
    wa
    1on
    dmdprdpr.t
    c1o
    cT
    cG
    con0
    dprdsn
    sylancr
    simprd
    eqtrd
    oveq12d
    eqtrd
end
