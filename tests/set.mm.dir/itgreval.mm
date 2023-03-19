include "citg.mm"
include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cfv.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "itgrevallem1.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "cibl.mm"
include "cmbf.mm"
include "w3a.mm"
include "iblrelem.mm"
include "mpbid.mm"
include "simp1d.mm"
include "mbfpos.mm"
include "ifan.mm"
include "mpteq2i.mm"
include "fveq2i.mm"
include "simp2d.mm"
include "syl5eqelr.mm"
include "max1.mm"
include "sylancr.mm"
include "iblpos.mm"
include "mpbir2and.mm"
include "itgposval.mm"
include "syl6eqr.mm"
include "renegcld.mm"
include "mbfneg.mm"
include "simp3d.mm"
include "oveq12d.mm"
include "eqtr4d.mm"

theorem itgreval
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume iblrelem.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume itgreval.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> S. A B _d x = ( S. A if ( 0 <_ B , B , 0 ) _d x - S. A if ( 0 <_ -u B , -u B , 0 ) _d x ) )

  proof
    wph
    vx
    cA
    cB
    citg
    vx
    cr
    vx
    cv
    cA
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    cB
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    vx
    cr
    @0
    cc0
    cB
    cneg
    #
    cle
    wbr
    #
    wa
    @5
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmin
    co
    vx
    cA
    @1
    cB
    cc0
    cif
    #
    citg
    #
    vx
    cA
    @6
    @5
    cc0
    cif
    #
    citg
    #
    cmin
    co
    wph
    vx
    cA
    cB
    iblrelem.1
    itgreval.2
    itgrevallem1
    wph
    @11
    @4
    @13
    @9
    cmin
    wph
    @11
    vx
    cr
    @0
    @10
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @4
    wph
    vx
    cA
    @10
    wph
    @0
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @10
    cr
    wcel
    iblrelem.1
    0re
    @1
    cB
    cc0
    cr
    ifcl
    sylancl
    #
    wph
    vx
    cA
    @10
    cmpt
    #
    cibl
    wcel
    @21
    cmbf
    wcel
    @16
    cr
    wcel
    wph
    vx
    cA
    cB
    iblrelem.1
    wph
    vx
    cA
    cB
    cmpt
    #
    cmbf
    wcel
    #
    @4
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    wph
    @22
    cibl
    wcel
    @23
    @24
    @25
    w3a
    itgreval.2
    wph
    vx
    cA
    cB
    iblrelem.1
    iblrelem
    mpbid
    #
    simp1d
    #
    mbfpos
    wph
    @16
    @4
    cr
    @3
    @15
    citg2
    vx
    cr
    @2
    @14
    @0
    @1
    cB
    cc0
    ifan
    mpteq2i
    fveq2i
    #
    wph
    @23
    @24
    @25
    @26
    simp2d
    syl5eqelr
    wph
    vx
    cA
    @10
    @20
    @17
    @19
    @18
    cc0
    @10
    cle
    wbr
    0re
    iblrelem.1
    cc0
    cB
    max1
    sylancr
    #
    iblpos
    mpbir2and
    @29
    itgposval
    @28
    syl6eqr
    wph
    @13
    vx
    cr
    @0
    @12
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @9
    wph
    vx
    cA
    @12
    @17
    @5
    cr
    wcel
    #
    @19
    @12
    cr
    wcel
    @17
    cB
    iblrelem.1
    renegcld
    #
    0re
    @6
    @5
    cc0
    cr
    ifcl
    sylancl
    #
    wph
    vx
    cA
    @12
    cmpt
    #
    cibl
    wcel
    @36
    cmbf
    wcel
    @32
    cr
    wcel
    wph
    vx
    cA
    @5
    @34
    wph
    vx
    cA
    cB
    cr
    iblrelem.1
    @27
    mbfneg
    mbfpos
    wph
    @32
    @9
    cr
    @8
    @31
    citg2
    vx
    cr
    @7
    @30
    @0
    @6
    @5
    cc0
    ifan
    mpteq2i
    fveq2i
    #
    wph
    @23
    @24
    @25
    @26
    simp3d
    syl5eqelr
    wph
    vx
    cA
    @12
    @35
    @17
    @19
    @33
    cc0
    @12
    cle
    wbr
    0re
    @34
    cc0
    @5
    max1
    sylancr
    #
    iblpos
    mpbir2and
    @38
    itgposval
    @37
    syl6eqr
    oveq12d
    eqtr4d
end
