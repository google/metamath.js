include "cvtxdg.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "cedg.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "wceq.mm"
include "cxad.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "cushgr.mm"
include "cvtx.mm"
include "cuspgr.mm"
include "1loopgruspgr.mm"
include "uspgrushgr.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "eqid.mm"
include "vtxdushgrfvedg.mm"
include "syl2anc.mm"
include "wex.mm"
include "c0.mm"
include "cif.mm"
include "snex.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "ceqsexv2d.mm"
include "a1i.mm"
include "snidg.mm"
include "iftrued.mm"
include "eqeq1d.mm"
include "exbidv.mm"
include "mpbird.mm"
include "1loopgredg.mm"
include "rabeqdv.mm"
include "eleq2.mm"
include "rabsnif.mm"
include "syl6eq.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "rabex.mm"
include "hash1snb.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "iftruei.mm"
include "eqeq1i.mm"
include "exbii.mm"
include "eqeq1.mm"
include "oveq12d.mm"
include "caddc.mm"
include "cr.mm"
include "1re.mm"
include "rexadd.mm"
include "mp2an.mm"
include "1p1e2.mm"
include "eqtri.mm"
include "3eqtrd.mm"

theorem 1loopgrvd2
  let wph: wff ph
  let cA: class A
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let vv: setvar v
  let va: setvar a
  let ve: setvar e
  assume 1loopgruspgr.v: |- ( ph -> ( Vtx ` G ) = V )
  assume 1loopgruspgr.a: |- ( ph -> A e. X )
  assume 1loopgruspgr.n: |- ( ph -> N e. V )
  assume 1loopgruspgr.i: |- ( ph -> ( iEdg ` G ) = { <. A , { N } >. } )


  assert |- ( ph -> ( ( VtxDeg ` G ) ` N ) = 2 )

  proof
    wph
    cN
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cN
    ve
    cv
    #
    wcel
    #
    ve
    cG
    cedg
    cfv
    #
    crab
    #
    chash
    cfv
    #
    @2
    cN
    csn
    #
    wceq
    #
    ve
    @4
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    c1
    c1
    cxad
    co
    #
    c2
    wph
    cG
    cushgr
    wcel
    #
    cN
    cG
    cvtx
    cfv
    #
    wcel
    @1
    @11
    wceq
    wph
    cG
    cuspgr
    wcel
    @13
    wph
    cA
    cG
    cN
    cV
    cX
    1loopgruspgr.v
    1loopgruspgr.a
    1loopgruspgr.n
    1loopgruspgr.i
    1loopgruspgr
    cG
    uspgrushgr
    syl
    wph
    cN
    cV
    @14
    1loopgruspgr.n
    1loopgruspgr.v
    eleqtrrd
    @0
    cN
    ve
    @4
    cG
    @14
    @14
    eqid
    @4
    eqid
    @0
    eqid
    vtxdushgrfvedg
    syl2anc
    wph
    @6
    c1
    @10
    c1
    cxad
    wph
    @5
    va
    cv
    #
    csn
    #
    wceq
    #
    va
    wex
    #
    @6
    c1
    wceq
    #
    wph
    @18
    cN
    @7
    wcel
    #
    @7
    csn
    #
    c0
    cif
    #
    @16
    wceq
    #
    va
    wex
    #
    wph
    @24
    @21
    @16
    wceq
    #
    va
    wex
    #
    @26
    wph
    @25
    @21
    @21
    wceq
    va
    @7
    cN
    snex
    @15
    @7
    wceq
    @16
    @21
    @21
    @15
    @7
    sneq
    eqeq2d
    @21
    eqid
    ceqsexv2d
    a1i
    #
    wph
    @23
    @25
    va
    wph
    @22
    @21
    @16
    wph
    @20
    @21
    c0
    wph
    cN
    cV
    wcel
    @20
    1loopgruspgr.n
    cN
    cV
    snidg
    syl
    iftrued
    eqeq1d
    exbidv
    mpbird
    wph
    @17
    @23
    va
    wph
    @5
    @22
    @16
    wph
    @5
    @3
    ve
    @21
    crab
    @22
    wph
    @3
    ve
    @4
    @21
    wph
    cA
    cG
    cN
    cV
    cX
    1loopgruspgr.v
    1loopgruspgr.a
    1loopgruspgr.n
    1loopgruspgr.i
    1loopgredg
    #
    rabeqdv
    @3
    @20
    ve
    @7
    @2
    @7
    cN
    eleq2
    rabsnif
    syl6eq
    eqeq1d
    exbidv
    mpbird
    @5
    cvv
    wcel
    @19
    @18
    wb
    @3
    ve
    @4
    cG
    cedg
    fvex
    #
    rabex
    @5
    cvv
    va
    hash1snb
    ax-mp
    sylibr
    wph
    @9
    @16
    wceq
    #
    va
    wex
    #
    @10
    c1
    wceq
    #
    wph
    @31
    @7
    @7
    wceq
    #
    @21
    c0
    cif
    #
    @16
    wceq
    #
    va
    wex
    #
    wph
    @26
    @36
    @27
    @35
    @25
    va
    @34
    @21
    @16
    @33
    @21
    c0
    @7
    eqid
    iftruei
    eqeq1i
    exbii
    sylibr
    wph
    @30
    @35
    va
    wph
    @9
    @34
    @16
    wph
    @9
    @8
    ve
    @21
    crab
    @34
    wph
    @8
    ve
    @4
    @21
    @28
    rabeqdv
    @8
    @33
    ve
    @7
    @2
    @7
    @7
    eqeq1
    rabsnif
    syl6eq
    eqeq1d
    exbidv
    mpbird
    @9
    cvv
    wcel
    @32
    @31
    wb
    @8
    ve
    @4
    @29
    rabex
    @9
    cvv
    va
    hash1snb
    ax-mp
    sylibr
    oveq12d
    @12
    c2
    wceq
    wph
    @12
    c1
    c1
    caddc
    co
    #
    c2
    c1
    cr
    wcel
    #
    @38
    @12
    @37
    wceq
    1re
    1re
    c1
    c1
    rexadd
    mp2an
    1p1e2
    eqtri
    a1i
    3eqtrd
end
