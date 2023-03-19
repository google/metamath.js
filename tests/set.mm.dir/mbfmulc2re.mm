include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cmbf.mm"
include "cvv.mm"
include "cr.mm"
include "cc.mm"
include "cdm.mm"
include "wf.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "wcel.mm"
include "dmexg.mm"
include "eqeltrrd.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "feqmptd.mm"
include "offval2.mm"
include "cre.mm"
include "cim.mm"
include "wa.mm"
include "remul2d.mm"
include "mpteq2dva.mm"
include "recld.mm"
include "eqidd.mm"
include "eqtr4d.mm"
include "ismbfcn2.mm"
include "mpbid.mm"
include "simpld.mm"
include "eqid.mm"
include "fmptd.mm"
include "mbfmulc2lem.mm"
include "eqeltrd.mm"
include "immul2d.mm"
include "imcld.mm"
include "simprd.mm"
include "recnd.mm"
include "mulcld.mm"
include "mpbir2and.mm"

theorem mbfmulc2re
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mbfmulc2re.1: |- ( ph -> F e. MblFn )
  assume mbfmulc2re.2: |- ( ph -> B e. RR )
  assume mbfmulc2re.3: |- ( ph -> F : A --> CC )


  assert |- ( ph -> ( ( A X. { B } ) oF x. F ) e. MblFn )

  proof
    wph
    cA
    cB
    csn
    cxp
    #
    cF
    cmul
    cof
    #
    co
    vx
    cA
    cB
    vx
    cv
    #
    cF
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cmbf
    wph
    vx
    cA
    cB
    @3
    cmul
    @0
    cF
    cvv
    cr
    cc
    wph
    cF
    cdm
    #
    cA
    cvv
    wph
    cA
    cc
    cF
    wf
    @6
    cA
    wceq
    mbfmulc2re.3
    cA
    cc
    cF
    fdm
    syl
    wph
    cF
    cmbf
    wcel
    @6
    cvv
    wcel
    mbfmulc2re.1
    cF
    cmbf
    dmexg
    syl
    eqeltrrd
    #
    wph
    cB
    cr
    wcel
    @2
    cA
    wcel
    #
    mbfmulc2re.2
    adantr
    #
    wph
    cA
    cc
    @2
    cF
    mbfmulc2re.3
    ffvelrnda
    #
    @0
    vx
    cA
    cB
    cmpt
    wceq
    wph
    vx
    cA
    cB
    fconstmpt
    a1i
    #
    wph
    vx
    cA
    cc
    cF
    mbfmulc2re.3
    feqmptd
    #
    offval2
    wph
    @5
    cmbf
    wcel
    vx
    cA
    @4
    cre
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    vx
    cA
    @4
    cim
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    wph
    @14
    @0
    vx
    cA
    @3
    cre
    cfv
    #
    cmpt
    #
    @1
    co
    #
    cmbf
    wph
    @14
    vx
    cA
    cB
    @17
    cmul
    co
    #
    cmpt
    @19
    wph
    vx
    cA
    @13
    @20
    wph
    @8
    wa
    #
    cB
    @3
    @9
    @10
    remul2d
    mpteq2dva
    wph
    vx
    cA
    cB
    @17
    cmul
    @0
    @18
    cvv
    cr
    cr
    @7
    @9
    @21
    @3
    @10
    recld
    #
    @11
    wph
    @18
    eqidd
    offval2
    eqtr4d
    wph
    cA
    cB
    @18
    wph
    @18
    cmbf
    wcel
    #
    vx
    cA
    @3
    cim
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    #
    wph
    vx
    cA
    @3
    cmpt
    #
    cmbf
    wcel
    @23
    @26
    wa
    wph
    cF
    @27
    cmbf
    @12
    mbfmulc2re.1
    eqeltrrd
    wph
    vx
    cA
    @3
    @10
    ismbfcn2
    mpbid
    #
    simpld
    mbfmulc2re.2
    wph
    vx
    cA
    @17
    cr
    @18
    @22
    @18
    eqid
    fmptd
    mbfmulc2lem
    eqeltrd
    wph
    @16
    @0
    @25
    @1
    co
    #
    cmbf
    wph
    @16
    vx
    cA
    cB
    @24
    cmul
    co
    #
    cmpt
    @29
    wph
    vx
    cA
    @15
    @30
    @21
    cB
    @3
    @9
    @10
    immul2d
    mpteq2dva
    wph
    vx
    cA
    cB
    @24
    cmul
    @0
    @25
    cvv
    cr
    cr
    @7
    @9
    @21
    @3
    @10
    imcld
    #
    @11
    wph
    @25
    eqidd
    offval2
    eqtr4d
    wph
    cA
    cB
    @25
    wph
    @23
    @26
    @28
    simprd
    mbfmulc2re.2
    wph
    vx
    cA
    @24
    cr
    @25
    @31
    @25
    eqid
    fmptd
    mbfmulc2lem
    eqeltrd
    wph
    vx
    cA
    @4
    @21
    cB
    @3
    wph
    cB
    cc
    wcel
    @8
    wph
    cB
    mbfmulc2re.2
    recnd
    adantr
    @10
    mulcld
    ismbfcn2
    mpbir2and
    eqeltrd
end
