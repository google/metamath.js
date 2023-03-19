include "cmpt.mm"
include "cmbf.mm"
include "wcel.mm"
include "cibl.mm"
include "cr.mm"
include "wa.mm"
include "w3a.mm"
include "wi.mm"
include "iblmbf.mm"
include "a1i.mm"
include "simp1.mm"
include "wb.mm"
include "cc.mm"
include "cc0.mm"
include "cif.mm"
include "cv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "citg2.mm"
include "cneg.mm"
include "cim.mm"
include "eqid.mm"
include "0cn.mm"
include "elimel.mm"
include "iblcnlem1.mm"
include "adantr.mm"
include "wceq.mm"
include "wral.mm"
include "wf.mm"
include "cdm.mm"
include "mbff.mm"
include "dmmptd.mm"
include "feq2d.mm"
include "biimpa.mm"
include "sylan2.mm"
include "fmpt.mm"
include "sylibr.mm"
include "iftrue.mm"
include "ralimi.mm"
include "syl.mm"
include "mpteq12.mm"
include "sylancr.mm"
include "eleq1d.mm"
include "imim2i.mm"
include "imp.mm"
include "fveq2d.mm"
include "ibllem.mm"
include "a1d.mm"
include "ralimi2.mm"
include "syl6eqr.mm"
include "negeqd.mm"
include "anbi12d.mm"
include "3anbi123d.mm"
include "3bitr3d.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem iblcnlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cV: class V
  let vk: setvar k
  assume itgcnlem.r: |- R = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ ( Re ` B ) ) , ( Re ` B ) , 0 ) ) )
  assume itgcnlem.s: |- S = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ -u ( Re ` B ) ) , -u ( Re ` B ) , 0 ) ) )
  assume itgcnlem.t: |- T = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ ( Im ` B ) ) , ( Im ` B ) , 0 ) ) )
  assume itgcnlem.u: |- U = ( S.2 ` ( x e. RR |-> if ( ( x e. A /\ 0 <_ -u ( Im ` B ) ) , -u ( Im ` B ) , 0 ) ) )
  assume itgcnlem.v: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint A x
  disjoint ph x
  disjoint V x
  disjoint k x
  disjoint A k
  disjoint B k
  disjoint k ph
  assert |- ( ph -> ( ( x e. A |-> B ) e. L^1 <-> ( ( x e. A |-> B ) e. MblFn /\ ( R e. RR /\ S e. RR ) /\ ( T e. RR /\ U e. RR ) ) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cmbf
    wcel
    #
    @0
    cibl
    wcel
    #
    @1
    cR
    cr
    wcel
    #
    cS
    cr
    wcel
    #
    wa
    #
    cT
    cr
    wcel
    #
    cU
    cr
    wcel
    #
    wa
    #
    w3a
    #
    @2
    @1
    wi
    wph
    @0
    iblmbf
    a1i
    @9
    @1
    wi
    wph
    @1
    @5
    @8
    simp1
    a1i
    wph
    @1
    @2
    @9
    wb
    wph
    @1
    wa
    #
    vx
    cA
    cB
    cc
    wcel
    #
    cB
    cc0
    cif
    #
    cmpt
    #
    cibl
    wcel
    #
    @13
    cmbf
    wcel
    #
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cc0
    @12
    cre
    cfv
    #
    cle
    wbr
    wa
    @18
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    vx
    cr
    @17
    cc0
    @18
    cneg
    #
    cle
    wbr
    wa
    @23
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vx
    cr
    @17
    cc0
    @12
    cim
    cfv
    #
    cle
    wbr
    wa
    @29
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    vx
    cr
    @17
    cc0
    @29
    cneg
    #
    cle
    wbr
    wa
    @34
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    wa
    #
    w3a
    #
    @2
    @9
    wph
    @14
    @40
    wb
    @1
    wph
    vx
    cA
    @12
    @21
    @26
    @32
    @37
    @21
    eqid
    @26
    eqid
    @32
    eqid
    @37
    eqid
    @12
    cc
    wcel
    wph
    @17
    wa
    cB
    cc0
    cc
    0cn
    elimel
    a1i
    iblcnlem1
    adantr
    @10
    @13
    @0
    cibl
    @10
    cA
    cA
    wceq
    @12
    cB
    wceq
    #
    vx
    cA
    wral
    #
    @13
    @0
    wceq
    cA
    eqid
    @10
    @11
    vx
    cA
    wral
    #
    @42
    @10
    cA
    cc
    @0
    wf
    #
    @43
    @1
    wph
    @0
    cdm
    #
    cc
    @0
    wf
    #
    @44
    @0
    mbff
    wph
    @46
    @44
    wph
    @45
    cA
    cc
    @0
    wph
    vx
    @0
    cA
    cB
    cV
    @0
    eqid
    #
    itgcnlem.v
    dmmptd
    feq2d
    biimpa
    sylan2
    vx
    cA
    cc
    cB
    @0
    @47
    fmpt
    sylibr
    #
    @11
    @41
    vx
    cA
    @11
    cB
    cc0
    iftrue
    #
    ralimi
    syl
    vx
    cA
    @12
    cA
    cB
    mpteq12
    sylancr
    #
    eleq1d
    @10
    @15
    @1
    @28
    @5
    @39
    @8
    @10
    @13
    @0
    cmbf
    @50
    eleq1d
    @10
    @22
    @3
    @27
    @4
    @10
    @21
    cR
    cr
    @10
    @21
    vx
    cr
    @17
    cc0
    cB
    cre
    cfv
    #
    cle
    wbr
    wa
    @51
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    cR
    @10
    @20
    @53
    citg2
    @10
    cr
    cr
    wceq
    #
    @19
    @52
    wceq
    #
    vx
    cr
    wral
    #
    @20
    @53
    wceq
    cr
    eqid
    #
    @10
    @43
    @56
    @48
    @11
    @55
    vx
    cA
    cr
    @17
    @11
    wi
    #
    @55
    @16
    cr
    wcel
    #
    @58
    vx
    cA
    @18
    @51
    @58
    @17
    wa
    #
    @12
    cB
    cre
    @58
    @17
    @41
    @11
    @41
    @17
    @49
    imim2i
    imp
    #
    fveq2d
    #
    ibllem
    a1d
    ralimi2
    syl
    vx
    cr
    @19
    cr
    @52
    mpteq12
    sylancr
    fveq2d
    itgcnlem.r
    syl6eqr
    eleq1d
    @10
    @26
    cS
    cr
    @10
    @26
    vx
    cr
    @17
    cc0
    @51
    cneg
    #
    cle
    wbr
    wa
    @63
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    cS
    @10
    @25
    @65
    citg2
    @10
    @54
    @24
    @64
    wceq
    #
    vx
    cr
    wral
    #
    @25
    @65
    wceq
    @57
    @10
    @43
    @67
    @48
    @11
    @66
    vx
    cA
    cr
    @58
    @66
    @59
    @58
    vx
    cA
    @23
    @63
    @60
    @18
    @51
    @62
    negeqd
    ibllem
    a1d
    ralimi2
    syl
    vx
    cr
    @24
    cr
    @64
    mpteq12
    sylancr
    fveq2d
    itgcnlem.s
    syl6eqr
    eleq1d
    anbi12d
    @10
    @33
    @6
    @38
    @7
    @10
    @32
    cT
    cr
    @10
    @32
    vx
    cr
    @17
    cc0
    cB
    cim
    cfv
    #
    cle
    wbr
    wa
    @68
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    cT
    @10
    @31
    @70
    citg2
    @10
    @54
    @30
    @69
    wceq
    #
    vx
    cr
    wral
    #
    @31
    @70
    wceq
    @57
    @10
    @43
    @72
    @48
    @11
    @71
    vx
    cA
    cr
    @58
    @71
    @59
    @58
    vx
    cA
    @29
    @68
    @60
    @12
    cB
    cim
    @61
    fveq2d
    #
    ibllem
    a1d
    ralimi2
    syl
    vx
    cr
    @30
    cr
    @69
    mpteq12
    sylancr
    fveq2d
    itgcnlem.t
    syl6eqr
    eleq1d
    @10
    @37
    cU
    cr
    @10
    @37
    vx
    cr
    @17
    cc0
    @68
    cneg
    #
    cle
    wbr
    wa
    @74
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    cU
    @10
    @36
    @76
    citg2
    @10
    @54
    @35
    @75
    wceq
    #
    vx
    cr
    wral
    #
    @36
    @76
    wceq
    @57
    @10
    @43
    @78
    @48
    @11
    @77
    vx
    cA
    cr
    @58
    @77
    @59
    @58
    vx
    cA
    @34
    @74
    @60
    @29
    @68
    @73
    negeqd
    ibllem
    a1d
    ralimi2
    syl
    vx
    cr
    @35
    cr
    @75
    mpteq12
    sylancr
    fveq2d
    itgcnlem.u
    syl6eqr
    eleq1d
    anbi12d
    3anbi123d
    3bitr3d
    ex
    pm5.21ndd
end
