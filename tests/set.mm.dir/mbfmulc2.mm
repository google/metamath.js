include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "cmbf.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cim.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "cneg.mm"
include "caddc.mm"
include "cvol.mm"
include "cdm.mm"
include "cc.mm"
include "cvv.mm"
include "mbfdm2.mm"
include "cv.mm"
include "wa.mm"
include "cr.mm"
include "recld.mm"
include "adantr.mm"
include "recnd.mm"
include "mbfmptcl.mm"
include "mulcld.mm"
include "ovexd.mm"
include "wceq.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "eqidd.mm"
include "offval2.mm"
include "imcld.mm"
include "renegcld.mm"
include "cmin.mm"
include "negsubd.mm"
include "mulneg1d.mm"
include "oveq2d.mm"
include "remuld.mm"
include "3eqtr4d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "ismbfcn2.mm"
include "mpbid.mm"
include "simpld.mm"
include "eqid.mm"
include "fmptd.mm"
include "mbfmulc2re.mm"
include "simprd.mm"
include "mbfadd.mm"
include "eqeltrrd.mm"
include "immuld.mm"
include "eqtr4d.mm"
include "mpbir2and.mm"

theorem mbfmulc2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume mbfmulc2.1: |- ( ph -> C e. CC )
  assume mbfmulc2.2: |- ( ( ph /\ x e. A ) -> B e. V )
  assume mbfmulc2.3: |- ( ph -> ( x e. A |-> B ) e. MblFn )

  disjoint A x
  disjoint C x
  disjoint ph x
  assert |- ( ph -> ( x e. A |-> ( C x. B ) ) e. MblFn )

  proof
    wph
    vx
    cA
    cC
    cB
    cmul
    co
    #
    cmpt
    cmbf
    wcel
    vx
    cA
    @0
    cre
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    vx
    cA
    @0
    cim
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    wph
    cA
    cC
    cre
    cfv
    #
    csn
    cxp
    #
    vx
    cA
    cB
    cre
    cfv
    #
    cmpt
    #
    cmul
    cof
    #
    co
    #
    cA
    cC
    cim
    cfv
    #
    cneg
    #
    csn
    cxp
    #
    vx
    cA
    cB
    cim
    cfv
    #
    cmpt
    #
    @9
    co
    #
    caddc
    cof
    #
    co
    #
    @2
    cmbf
    wph
    @18
    vx
    cA
    @5
    @7
    cmul
    co
    #
    @12
    @14
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    @2
    wph
    vx
    cA
    @19
    @20
    caddc
    @10
    @16
    cvol
    cdm
    #
    cc
    cvv
    wph
    vx
    cA
    cB
    cV
    mbfmulc2.3
    mbfmulc2.2
    mbfdm2
    #
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    @5
    @7
    @25
    @5
    wph
    @5
    cr
    wcel
    @24
    wph
    cC
    mbfmulc2.1
    recld
    #
    adantr
    #
    recnd
    @25
    @7
    @25
    cB
    wph
    vx
    cA
    cB
    cV
    mbfmulc2.3
    mbfmulc2.2
    mbfmptcl
    #
    recld
    #
    recnd
    #
    mulcld
    #
    @25
    @12
    @14
    cmul
    ovexd
    wph
    vx
    cA
    @5
    @7
    cmul
    @6
    @8
    @22
    cr
    cr
    @23
    @27
    @29
    @6
    vx
    cA
    @5
    cmpt
    wceq
    wph
    vx
    cA
    @5
    fconstmpt
    a1i
    #
    wph
    @8
    eqidd
    #
    offval2
    wph
    vx
    cA
    @12
    @14
    cmul
    @13
    @15
    @22
    cr
    cr
    @23
    wph
    @12
    cr
    wcel
    @24
    wph
    @11
    wph
    cC
    mbfmulc2.1
    imcld
    #
    renegcld
    #
    adantr
    @25
    cB
    @28
    imcld
    #
    @13
    vx
    cA
    @12
    cmpt
    wceq
    wph
    vx
    cA
    @12
    fconstmpt
    a1i
    wph
    @15
    eqidd
    #
    offval2
    offval2
    wph
    vx
    cA
    @21
    @1
    @25
    @19
    @11
    @14
    cmul
    co
    #
    cneg
    #
    caddc
    co
    @19
    @38
    cmin
    co
    @21
    @1
    @25
    @19
    @38
    @31
    @25
    @11
    @14
    @25
    @11
    wph
    @11
    cr
    wcel
    @24
    @34
    adantr
    #
    recnd
    #
    @25
    @14
    @36
    recnd
    #
    mulcld
    negsubd
    @25
    @20
    @39
    @19
    caddc
    @25
    @11
    @14
    @41
    @42
    mulneg1d
    oveq2d
    @25
    cC
    cB
    wph
    cC
    cc
    wcel
    @24
    mbfmulc2.1
    adantr
    #
    @28
    remuld
    3eqtr4d
    mpteq2dva
    eqtrd
    wph
    @10
    @16
    wph
    cA
    @5
    @8
    wph
    @8
    cmbf
    wcel
    #
    @15
    cmbf
    wcel
    #
    wph
    vx
    cA
    cB
    cmpt
    cmbf
    wcel
    @44
    @45
    wa
    mbfmulc2.3
    wph
    vx
    cA
    cB
    @28
    ismbfcn2
    mpbid
    #
    simpld
    #
    @26
    wph
    vx
    cA
    @7
    cc
    @8
    @30
    @8
    eqid
    fmptd
    #
    mbfmulc2re
    wph
    cA
    @12
    @15
    wph
    @44
    @45
    @46
    simprd
    #
    @35
    wph
    vx
    cA
    @14
    cc
    @15
    @42
    @15
    eqid
    fmptd
    #
    mbfmulc2re
    mbfadd
    eqeltrrd
    wph
    @6
    @15
    @9
    co
    #
    cA
    @11
    csn
    cxp
    #
    @8
    @9
    co
    #
    @17
    co
    #
    @4
    cmbf
    wph
    @54
    vx
    cA
    @5
    @14
    cmul
    co
    #
    @11
    @7
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    @4
    wph
    vx
    cA
    @55
    @56
    caddc
    @51
    @53
    @22
    cvv
    cvv
    @23
    @25
    @5
    @14
    cmul
    ovexd
    @25
    @11
    @7
    cmul
    ovexd
    wph
    vx
    cA
    @5
    @14
    cmul
    @6
    @15
    @22
    cr
    cr
    @23
    @27
    @36
    @32
    @37
    offval2
    wph
    vx
    cA
    @11
    @7
    cmul
    @52
    @8
    @22
    cr
    cr
    @23
    @40
    @29
    @52
    vx
    cA
    @11
    cmpt
    wceq
    wph
    vx
    cA
    @11
    fconstmpt
    a1i
    @33
    offval2
    offval2
    wph
    vx
    cA
    @3
    @57
    @25
    cC
    cB
    @43
    @28
    immuld
    mpteq2dva
    eqtr4d
    wph
    @51
    @53
    wph
    cA
    @5
    @15
    @49
    @26
    @50
    mbfmulc2re
    wph
    cA
    @11
    @8
    @47
    @34
    @48
    mbfmulc2re
    mbfadd
    eqeltrrd
    wph
    vx
    cA
    @0
    @25
    cC
    cB
    @43
    @28
    mulcld
    ismbfcn2
    mpbir2and
end
