include "caddc.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "citg.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmpt.mm"
include "cibl.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "readdd.mm"
include "itgeq2dv.mm"
include "cr.mm"
include "recld.mm"
include "iblcn.mm"
include "mpbid.mm"
include "simpld.mm"
include "itgaddlem2.mm"
include "eqtrd.mm"
include "imaddd.mm"
include "imcld.mm"
include "simprd.mm"
include "oveq2d.mm"
include "cc.mm"
include "ax-icn.mm"
include "a1i.mm"
include "itgcl.mm"
include "adddid.mm"
include "oveq12d.mm"
include "mulcl.mm"
include "sylancr.mm"
include "add4d.mm"
include "cvv.mm"
include "ovexd.mm"
include "ibladd.mm"
include "itgcnval.mm"
include "3eqtr4d.mm"

theorem itgadd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume itgadd.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgadd.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume itgadd.3: |- ( ( ph /\ x e. A ) -> C e. V )
  assume itgadd.4: |- ( ph -> ( x e. A |-> C ) e. L^1 )

  disjoint A x
  disjoint V x
  disjoint ph x
  assert |- ( ph -> S. A ( B + C ) _d x = ( S. A B _d x + S. A C _d x ) )

  proof
    wph
    vx
    cA
    cB
    cC
    caddc
    co
    #
    cre
    cfv
    #
    citg
    #
    ci
    vx
    cA
    @0
    cim
    cfv
    #
    citg
    #
    cmul
    co
    #
    caddc
    co
    #
    vx
    cA
    cB
    cre
    cfv
    #
    citg
    #
    ci
    vx
    cA
    cB
    cim
    cfv
    #
    citg
    #
    cmul
    co
    #
    caddc
    co
    #
    vx
    cA
    cC
    cre
    cfv
    #
    citg
    #
    ci
    vx
    cA
    cC
    cim
    cfv
    #
    citg
    #
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    vx
    cA
    @0
    citg
    vx
    cA
    cB
    citg
    #
    vx
    cA
    cC
    citg
    #
    caddc
    co
    wph
    @6
    @8
    @14
    caddc
    co
    #
    @11
    @17
    caddc
    co
    #
    caddc
    co
    @19
    wph
    @2
    @22
    @5
    @23
    caddc
    wph
    @2
    vx
    cA
    @7
    @13
    caddc
    co
    #
    citg
    @22
    wph
    vx
    cA
    @1
    @24
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cB
    cC
    wph
    vx
    cA
    cB
    cV
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    #
    @26
    cmbf
    wcel
    itgadd.2
    @26
    iblmbf
    syl
    itgadd.1
    mbfmptcl
    #
    wph
    vx
    cA
    cC
    cV
    wph
    vx
    cA
    cC
    cmpt
    #
    cibl
    wcel
    #
    @29
    cmbf
    wcel
    itgadd.4
    @29
    iblmbf
    syl
    itgadd.3
    mbfmptcl
    #
    readdd
    itgeq2dv
    wph
    vx
    cA
    @7
    @13
    cr
    @25
    cB
    @28
    recld
    #
    wph
    vx
    cA
    @7
    cmpt
    cibl
    wcel
    #
    vx
    cA
    @9
    cmpt
    cibl
    wcel
    #
    wph
    @27
    @33
    @34
    wa
    itgadd.2
    wph
    vx
    cA
    cB
    @28
    iblcn
    mpbid
    #
    simpld
    #
    @25
    cC
    @31
    recld
    #
    wph
    vx
    cA
    @13
    cmpt
    cibl
    wcel
    #
    vx
    cA
    @15
    cmpt
    cibl
    wcel
    #
    wph
    @30
    @38
    @39
    wa
    itgadd.4
    wph
    vx
    cA
    cC
    @31
    iblcn
    mpbid
    #
    simpld
    #
    @32
    @37
    itgaddlem2
    eqtrd
    wph
    @5
    ci
    @10
    @16
    caddc
    co
    #
    cmul
    co
    @23
    wph
    @4
    @42
    ci
    cmul
    wph
    @4
    vx
    cA
    @9
    @15
    caddc
    co
    #
    citg
    @42
    wph
    vx
    cA
    @3
    @43
    @25
    cB
    cC
    @28
    @31
    imaddd
    itgeq2dv
    wph
    vx
    cA
    @9
    @15
    cr
    @25
    cB
    @28
    imcld
    #
    wph
    @33
    @34
    @35
    simprd
    #
    @25
    cC
    @31
    imcld
    #
    wph
    @38
    @39
    @40
    simprd
    #
    @44
    @46
    itgaddlem2
    eqtrd
    oveq2d
    wph
    ci
    @10
    @16
    ci
    cc
    wcel
    #
    wph
    ax-icn
    a1i
    wph
    vx
    cA
    @9
    cr
    @44
    @45
    itgcl
    #
    wph
    vx
    cA
    @15
    cr
    @46
    @47
    itgcl
    #
    adddid
    eqtrd
    oveq12d
    wph
    @8
    @14
    @11
    @17
    wph
    vx
    cA
    @7
    cr
    @32
    @36
    itgcl
    wph
    vx
    cA
    @13
    cr
    @37
    @41
    itgcl
    wph
    @48
    @10
    cc
    wcel
    @11
    cc
    wcel
    ax-icn
    @49
    ci
    @10
    mulcl
    sylancr
    wph
    @48
    @16
    cc
    wcel
    @17
    cc
    wcel
    ax-icn
    @50
    ci
    @16
    mulcl
    sylancr
    add4d
    eqtrd
    wph
    vx
    cA
    @0
    cvv
    @25
    cB
    cC
    caddc
    ovexd
    wph
    vx
    cA
    cB
    cC
    cV
    itgadd.1
    itgadd.2
    itgadd.3
    itgadd.4
    ibladd
    itgcnval
    wph
    @20
    @12
    @21
    @18
    caddc
    wph
    vx
    cA
    cB
    cV
    itgadd.1
    itgadd.2
    itgcnval
    wph
    vx
    cA
    cC
    cV
    itgadd.3
    itgadd.4
    itgcnval
    oveq12d
    3eqtr4d
end
