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
include "ccom.mm"
include "cc.mm"
include "addcld.mm"
include "eqidd.mm"
include "wf.mm"
include "ref.mm"
include "a1i.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "wb.mm"
include "eqid.mm"
include "fmptd.mm"
include "ismbfcn.mm"
include "eqeltrrd.mm"
include "itgaddnclem2.mm"
include "imaddd.mm"
include "imcld.mm"
include "simprd.mm"
include "imf.mm"
include "oveq2d.mm"
include "ax-icn.mm"
include "itgcl.mm"
include "adddid.mm"
include "oveq12d.mm"
include "mulcl.mm"
include "sylancr.mm"
include "add4d.mm"
include "cvv.mm"
include "ovexd.mm"
include "ibladdnc.mm"
include "itgcnval.mm"
include "3eqtr4d.mm"

theorem itgaddnc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y
  assume ibladdnc.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume ibladdnc.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume ibladdnc.3: |- ( ( ph /\ x e. A ) -> C e. V )
  assume ibladdnc.4: |- ( ph -> ( x e. A |-> C ) e. L^1 )
  assume ibladdnc.m: |- ( ph -> ( x e. A |-> ( B + C ) ) e. MblFn )

  disjoint A x
  disjoint V x
  disjoint ph x
  disjoint x y
  disjoint B y
  disjoint C y
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
    ibladdnc.2
    @26
    iblmbf
    syl
    ibladdnc.1
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
    ibladdnc.4
    @29
    iblmbf
    syl
    ibladdnc.3
    mbfmptcl
    #
    readdd
    #
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
    @34
    @35
    wa
    ibladdnc.2
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
    @39
    @40
    wa
    ibladdnc.4
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
    wph
    cre
    vx
    cA
    @0
    cmpt
    #
    ccom
    #
    vx
    cA
    @24
    cmpt
    #
    cmbf
    wph
    @44
    vx
    cA
    @1
    cmpt
    @45
    wph
    vx
    vy
    cA
    cc
    @0
    vy
    cv
    #
    cre
    cfv
    @1
    @43
    cre
    @25
    cB
    cC
    @28
    @31
    addcld
    #
    wph
    @43
    eqidd
    #
    wph
    vy
    cc
    cr
    cre
    cc
    cr
    cre
    wf
    wph
    ref
    a1i
    feqmptd
    @46
    @0
    cre
    fveq2
    fmptco
    wph
    vx
    cA
    @1
    @24
    @32
    mpteq2dva
    eqtrd
    wph
    @44
    cmbf
    wcel
    #
    cim
    @43
    ccom
    #
    cmbf
    wcel
    #
    wph
    @43
    cmbf
    wcel
    #
    @49
    @51
    wa
    #
    ibladdnc.m
    wph
    cA
    cc
    @43
    wf
    @52
    @53
    wb
    wph
    vx
    cA
    @0
    cc
    @43
    @47
    @43
    eqid
    fmptd
    cA
    @43
    ismbfcn
    syl
    mpbid
    #
    simpld
    eqeltrrd
    @33
    @38
    itgaddnclem2
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
    @55
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
    @55
    wph
    vx
    cA
    @3
    @56
    @25
    cB
    cC
    @28
    @31
    imaddd
    #
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
    @34
    @35
    @36
    simprd
    #
    @25
    cC
    @31
    imcld
    #
    wph
    @39
    @40
    @41
    simprd
    #
    wph
    @50
    vx
    cA
    @56
    cmpt
    #
    cmbf
    wph
    @50
    vx
    cA
    @3
    cmpt
    @62
    wph
    vx
    vy
    cA
    cc
    @0
    @46
    cim
    cfv
    @3
    @43
    cim
    @47
    @48
    wph
    vy
    cc
    cr
    cim
    cc
    cr
    cim
    wf
    wph
    imf
    a1i
    feqmptd
    @46
    @0
    cim
    fveq2
    fmptco
    wph
    vx
    cA
    @3
    @56
    @57
    mpteq2dva
    eqtrd
    wph
    @49
    @51
    @54
    simprd
    eqeltrrd
    @58
    @60
    itgaddnclem2
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
    @58
    @59
    itgcl
    #
    wph
    vx
    cA
    @15
    cr
    @60
    @61
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
    @33
    @37
    itgcl
    wph
    vx
    cA
    @13
    cr
    @38
    @42
    itgcl
    wph
    @63
    @10
    cc
    wcel
    @11
    cc
    wcel
    ax-icn
    @64
    ci
    @10
    mulcl
    sylancr
    wph
    @63
    @16
    cc
    wcel
    @17
    cc
    wcel
    ax-icn
    @65
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
    ibladdnc.1
    ibladdnc.2
    ibladdnc.3
    ibladdnc.4
    ibladdnc.m
    ibladdnc
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
    ibladdnc.1
    ibladdnc.2
    itgcnval
    wph
    vx
    cA
    cC
    cV
    ibladdnc.3
    ibladdnc.4
    itgcnval
    oveq12d
    3eqtr4d
end
