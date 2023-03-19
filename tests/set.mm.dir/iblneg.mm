include "cneg.mm"
include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cim.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cv.mm"
include "wa.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfmptcl.mm"
include "renegd.mm"
include "breq2d.mm"
include "ifbieq1d.mm"
include "mpteq2dva.mm"
include "iblcn.mm"
include "mpbid.mm"
include "simpld.mm"
include "recld.mm"
include "iblre.mm"
include "simprd.mm"
include "eqeltrd.mm"
include "negeqd.mm"
include "recnd.mm"
include "negnegd.mm"
include "eqtrd.mm"
include "negcld.mm"
include "mpbir2and.mm"
include "imnegd.mm"
include "imcld.mm"

theorem iblneg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume itgcnval.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgcnval.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )

  disjoint A x
  disjoint ph x
  disjoint V x
  assert |- ( ph -> ( x e. A |-> -u B ) e. L^1 )

  proof
    wph
    vx
    cA
    cB
    cneg
    #
    cmpt
    cibl
    wcel
    vx
    cA
    @0
    cre
    cfv
    #
    cmpt
    cibl
    wcel
    #
    vx
    cA
    @0
    cim
    cfv
    #
    cmpt
    cibl
    wcel
    #
    wph
    @2
    vx
    cA
    cc0
    @1
    cle
    wbr
    #
    @1
    cc0
    cif
    #
    cmpt
    #
    cibl
    wcel
    vx
    cA
    cc0
    @1
    cneg
    #
    cle
    wbr
    #
    @8
    cc0
    cif
    #
    cmpt
    #
    cibl
    wcel
    wph
    @7
    vx
    cA
    cc0
    cB
    cre
    cfv
    #
    cneg
    #
    cle
    wbr
    #
    @13
    cc0
    cif
    #
    cmpt
    #
    cibl
    wph
    vx
    cA
    @6
    @15
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    @5
    @14
    @1
    @13
    cc0
    @17
    @1
    @13
    cc0
    cle
    @17
    cB
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
    @18
    cmbf
    wcel
    itgcnval.2
    @18
    iblmbf
    syl
    itgcnval.1
    mbfmptcl
    #
    renegd
    #
    breq2d
    @21
    ifbieq1d
    mpteq2dva
    wph
    vx
    cA
    cc0
    @12
    cle
    wbr
    #
    @12
    cc0
    cif
    #
    cmpt
    #
    cibl
    wcel
    #
    @16
    cibl
    wcel
    #
    wph
    vx
    cA
    @12
    cmpt
    cibl
    wcel
    #
    @25
    @26
    wa
    wph
    @27
    vx
    cA
    cB
    cim
    cfv
    #
    cmpt
    cibl
    wcel
    #
    wph
    @19
    @27
    @29
    wa
    itgcnval.2
    wph
    vx
    cA
    cB
    @20
    iblcn
    mpbid
    #
    simpld
    wph
    vx
    cA
    @12
    @17
    cB
    @20
    recld
    #
    iblre
    mpbid
    #
    simprd
    eqeltrd
    wph
    @11
    @24
    cibl
    wph
    vx
    cA
    @10
    @23
    @17
    @9
    @22
    @8
    @12
    cc0
    @17
    @8
    @12
    cc0
    cle
    @17
    @8
    @13
    cneg
    @12
    @17
    @1
    @13
    @21
    negeqd
    @17
    @12
    @17
    @12
    @31
    recnd
    negnegd
    eqtrd
    #
    breq2d
    @33
    ifbieq1d
    mpteq2dva
    wph
    @25
    @26
    @32
    simpld
    eqeltrd
    wph
    vx
    cA
    @1
    @17
    @0
    @17
    cB
    @20
    negcld
    #
    recld
    iblre
    mpbir2and
    wph
    @4
    vx
    cA
    cc0
    @3
    cle
    wbr
    #
    @3
    cc0
    cif
    #
    cmpt
    #
    cibl
    wcel
    vx
    cA
    cc0
    @3
    cneg
    #
    cle
    wbr
    #
    @38
    cc0
    cif
    #
    cmpt
    #
    cibl
    wcel
    wph
    @37
    vx
    cA
    cc0
    @28
    cneg
    #
    cle
    wbr
    #
    @42
    cc0
    cif
    #
    cmpt
    #
    cibl
    wph
    vx
    cA
    @36
    @44
    @17
    @35
    @43
    @3
    @42
    cc0
    @17
    @3
    @42
    cc0
    cle
    @17
    cB
    @20
    imnegd
    #
    breq2d
    @46
    ifbieq1d
    mpteq2dva
    wph
    vx
    cA
    cc0
    @28
    cle
    wbr
    #
    @28
    cc0
    cif
    #
    cmpt
    #
    cibl
    wcel
    #
    @45
    cibl
    wcel
    #
    wph
    @29
    @50
    @51
    wa
    wph
    @27
    @29
    @30
    simprd
    wph
    vx
    cA
    @28
    @17
    cB
    @20
    imcld
    #
    iblre
    mpbid
    #
    simprd
    eqeltrd
    wph
    @41
    @49
    cibl
    wph
    vx
    cA
    @40
    @48
    @17
    @39
    @47
    @38
    @28
    cc0
    @17
    @38
    @28
    cc0
    cle
    @17
    @38
    @42
    cneg
    @28
    @17
    @3
    @42
    @46
    negeqd
    @17
    @28
    @17
    @28
    @52
    recnd
    negnegd
    eqtrd
    #
    breq2d
    @54
    ifbieq1d
    mpteq2dva
    wph
    @50
    @51
    @53
    simpld
    eqeltrd
    wph
    vx
    cA
    @3
    @17
    @0
    @34
    imcld
    iblre
    mpbir2and
    wph
    vx
    cA
    @0
    @34
    iblcn
    mpbir2and
end
