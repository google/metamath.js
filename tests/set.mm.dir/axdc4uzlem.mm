include "wcel.mm"
include "cxp.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wa.mm"
include "com.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "csuc.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "c1.mm"
include "caddc.mm"
include "wf1o.mm"
include "cuz.mm"
include "om2uzf1oi.mm"
include "wb.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "f1of.mm"
include "ffvelrni.mm"
include "fovrn.mm"
include "syl3an2.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "axdc4.mm"
include "sylan2.mm"
include "ccnv.mm"
include "ccom.mm"
include "f1ocnv.mm"
include "mp2b.mm"
include "fco.mm"
include "mpan2.mm"
include "3ad2ant1.mm"
include "cz.mm"
include "uzid.mm"
include "eleqtrri.mm"
include "fvco3.mm"
include "mp2an.mm"
include "om2uz0i.mm"
include "wi.mm"
include "peano1.mm"
include "f1ocnvfv.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "simp2.mm"
include "syl5eq.mm"
include "adantl.mm"
include "suceq.mm"
include "fveq2d.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "syl.mm"
include "peano2uzs.mm"
include "sylancr.mm"
include "om2uzsuci.mm"
include "f1ocnvfv2.mm"
include "mpan.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "peano2.mm"
include "mpd.mm"
include "eqtr2d.mm"
include "ffvelrn.mm"
include "oveq2.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "sylibd.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "3adant2.mm"
include "vex.mm"
include "cvv.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "wfun.mm"
include "rdgfun.mm"
include "omex.mm"
include "resfunexg.mm"
include "eqeltri.mm"
include "cnvex.mm"
include "coex.mm"
include "feq1.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "oveq2d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "spcev.mm"
include "syl3anc.mm"
include "exlimiv.mm"

theorem axdc4uzlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vf: setvar f
  assume axdc4uz.1: |- M e. ZZ
  assume axdc4uz.2: |- Z = ( ZZ>= ` M )
  assume axdc4uz.3: |- A e. _V
  assume axdc4uz.4: |- G = ( rec ( ( y e. _V |-> ( y + 1 ) ) , M ) |` _om )
  assume axdc4uz.5: |- H = ( n e. _om , x e. A |-> ( ( G ` n ) F x ) )

  disjoint g k
  disjoint g n
  disjoint g x
  disjoint G g
  disjoint k n
  disjoint k x
  disjoint G k
  disjoint n x
  disjoint G n
  disjoint G x
  disjoint H k
  disjoint g k
  disjoint g n
  disjoint g x
  disjoint A g
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint C g
  disjoint F g
  disjoint F k
  disjoint F n
  disjoint F x
  disjoint g y
  disjoint M g
  disjoint k y
  disjoint M k
  disjoint n y
  disjoint M n
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint Z g
  disjoint Z n
  disjoint Z x
  disjoint g m
  disjoint k m
  disjoint m n
  disjoint m x
  disjoint G m
  disjoint f k
  disjoint f m
  disjoint H f
  disjoint H m
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint A f
  disjoint g m
  disjoint k m
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint C f
  disjoint C m
  disjoint F f
  disjoint f y
  disjoint M f
  disjoint Z f
  assert |- ( ( C e. A /\ F : ( Z X. A ) --> ( ~P A \ { (/) } ) ) -> E. g ( g : Z --> A /\ ( g ` M ) = C /\ A. k e. Z ( g ` ( k + 1 ) ) e. ( k F ( g ` k ) ) ) )

  proof
    cC
    cA
    wcel
    #
    cZ
    cA
    cxp
    cA
    cpw
    c0
    csn
    cdif
    #
    cF
    wf
    #
    wa
    com
    cA
    vf
    cv
    #
    wf
    #
    c0
    @3
    cfv
    #
    cC
    wceq
    #
    vm
    cv
    #
    csuc
    #
    @3
    cfv
    #
    @7
    @7
    @3
    cfv
    #
    cH
    co
    #
    wcel
    #
    vm
    com
    wral
    #
    w3a
    #
    vf
    wex
    #
    cZ
    cA
    vg
    cv
    #
    wf
    #
    cM
    @16
    cfv
    #
    cC
    wceq
    #
    vk
    cv
    #
    c1
    caddc
    co
    #
    @16
    cfv
    #
    @20
    @20
    @16
    cfv
    #
    cF
    co
    #
    wcel
    #
    vk
    cZ
    wral
    #
    w3a
    #
    vg
    wex
    #
    @2
    @0
    com
    cA
    cxp
    @1
    cH
    wf
    #
    @15
    @2
    vn
    cv
    #
    cG
    cfv
    #
    vx
    cv
    #
    cF
    co
    #
    @1
    wcel
    #
    vx
    cA
    wral
    vn
    com
    wral
    @29
    @2
    @34
    vn
    vx
    com
    cA
    @2
    @30
    com
    wcel
    #
    @32
    cA
    wcel
    #
    @34
    @35
    @2
    @31
    cZ
    wcel
    @36
    @34
    com
    cZ
    @30
    cG
    com
    cZ
    cG
    wf1o
    #
    com
    cZ
    cG
    wf
    @37
    com
    cM
    cuz
    cfv
    #
    cG
    wf1o
    #
    vy
    cM
    cG
    axdc4uz.1
    axdc4uz.4
    om2uzf1oi
    cZ
    @38
    wceq
    @37
    @39
    wb
    axdc4uz.2
    cZ
    @38
    com
    cG
    f1oeq3
    ax-mp
    mpbir
    #
    com
    cZ
    cG
    f1of
    ax-mp
    ffvelrni
    @31
    @32
    @1
    cZ
    cA
    cF
    fovrn
    syl3an2
    3expb
    ralrimivva
    vn
    vx
    com
    cA
    @33
    @1
    cH
    axdc4uz.5
    fmpt2
    sylib
    cA
    cC
    vf
    vm
    cH
    axdc4uz.3
    axdc4
    sylan2
    @14
    @28
    vf
    @14
    cZ
    cA
    @3
    cG
    ccnv
    #
    ccom
    #
    wf
    #
    cM
    @42
    cfv
    #
    cC
    wceq
    #
    @21
    @42
    cfv
    #
    @20
    @20
    @42
    cfv
    #
    cF
    co
    #
    wcel
    #
    vk
    cZ
    wral
    #
    @28
    @4
    @6
    @43
    @13
    @4
    cZ
    com
    @41
    wf
    #
    @43
    @37
    cZ
    com
    @41
    wf1o
    @51
    @40
    com
    cZ
    cG
    f1ocnv
    cZ
    com
    @41
    f1of
    mp2b
    #
    cZ
    com
    cA
    @3
    @41
    fco
    mpan2
    3ad2ant1
    @14
    @44
    @5
    cC
    @44
    cM
    @41
    cfv
    #
    @3
    cfv
    #
    @5
    @51
    cM
    cZ
    wcel
    @44
    @54
    wceq
    @52
    cM
    @38
    cZ
    cM
    cz
    wcel
    cM
    @38
    wcel
    axdc4uz.1
    cM
    uzid
    ax-mp
    axdc4uz.2
    eleqtrri
    cZ
    com
    cM
    @3
    @41
    fvco3
    mp2an
    @53
    c0
    @3
    c0
    cG
    cfv
    cM
    wceq
    #
    @53
    c0
    wceq
    #
    vy
    cM
    cG
    axdc4uz.1
    axdc4uz.4
    om2uz0i
    @37
    c0
    com
    wcel
    @55
    @56
    wi
    @40
    peano1
    com
    cZ
    c0
    cM
    cG
    f1ocnvfv
    mp2an
    ax-mp
    fveq2i
    eqtri
    @4
    @6
    @13
    simp2
    syl5eq
    @4
    @13
    @50
    @6
    @4
    @13
    wa
    @49
    vk
    cZ
    @4
    @20
    cZ
    wcel
    #
    @13
    @49
    @4
    @57
    wa
    #
    @13
    @20
    @41
    cfv
    #
    csuc
    #
    @3
    cfv
    #
    @59
    @59
    @3
    cfv
    #
    cH
    co
    #
    wcel
    #
    @49
    @58
    @59
    com
    wcel
    #
    @13
    @64
    wi
    @57
    @65
    @4
    cZ
    com
    @20
    @41
    @52
    ffvelrni
    #
    adantl
    #
    @12
    @64
    vm
    @59
    com
    @7
    @59
    wceq
    #
    @9
    @61
    @11
    @63
    @68
    @8
    @60
    @3
    @7
    @59
    suceq
    fveq2d
    @68
    @7
    @59
    @10
    @62
    cH
    @68
    id
    @7
    @59
    @3
    fveq2
    oveq12d
    eleq12d
    rspcv
    syl
    @58
    @61
    @46
    @63
    @48
    @57
    @61
    @46
    wceq
    @4
    @57
    @46
    @21
    @41
    cfv
    #
    @3
    cfv
    #
    @61
    @57
    @51
    @21
    cZ
    wcel
    @46
    @70
    wceq
    @52
    cM
    @20
    cZ
    axdc4uz.2
    peano2uzs
    cZ
    com
    @21
    @3
    @41
    fvco3
    sylancr
    @57
    @69
    @60
    @3
    @57
    @60
    cG
    cfv
    #
    @21
    wceq
    #
    @69
    @60
    wceq
    #
    @57
    @71
    @59
    cG
    cfv
    #
    c1
    caddc
    co
    #
    @21
    @57
    @65
    @71
    @75
    wceq
    @66
    vy
    @59
    cM
    cG
    axdc4uz.1
    axdc4uz.4
    om2uzsuci
    syl
    @57
    @74
    @20
    c1
    caddc
    @37
    @57
    @74
    @20
    wceq
    @40
    com
    cZ
    @20
    cG
    f1ocnvfv2
    mpan
    #
    oveq1d
    eqtrd
    @57
    @37
    @60
    com
    wcel
    #
    @72
    @73
    wi
    @40
    @57
    @65
    @77
    @66
    @59
    peano2
    syl
    com
    cZ
    @60
    @21
    cG
    f1ocnvfv
    sylancr
    mpd
    fveq2d
    eqtr2d
    adantl
    @58
    @63
    @74
    @62
    cF
    co
    #
    @48
    @58
    @65
    @62
    cA
    wcel
    #
    @63
    @78
    wceq
    @67
    @57
    @4
    @65
    @79
    @66
    com
    cA
    @59
    @3
    ffvelrn
    sylan2
    vn
    vx
    @59
    @62
    com
    cA
    @33
    @78
    cH
    @74
    @32
    cF
    co
    @30
    @59
    wceq
    @31
    @74
    @32
    cF
    @30
    @59
    cG
    fveq2
    oveq1d
    @32
    @62
    @74
    cF
    oveq2
    axdc4uz.5
    @74
    @62
    cF
    ovex
    ovmpt2
    syl2anc
    @57
    @78
    @48
    wceq
    @4
    @57
    @74
    @20
    @62
    @47
    cF
    @76
    @57
    @47
    @62
    @51
    @57
    @47
    @62
    wceq
    @52
    cZ
    com
    @20
    @3
    @41
    fvco3
    mpan
    eqcomd
    oveq12d
    adantl
    eqtrd
    eleq12d
    sylibd
    impancom
    ralrimiv
    3adant2
    @27
    @43
    @45
    @50
    w3a
    vg
    @42
    @3
    @41
    vf
    vex
    cG
    cG
    vy
    cvv
    vy
    cv
    c1
    caddc
    co
    cmpt
    #
    cM
    crdg
    #
    com
    cres
    #
    cvv
    axdc4uz.4
    @81
    wfun
    com
    cvv
    wcel
    @82
    cvv
    wcel
    cM
    @80
    rdgfun
    omex
    @81
    com
    cvv
    resfunexg
    mp2an
    eqeltri
    cnvex
    coex
    @16
    @42
    wceq
    #
    @17
    @43
    @19
    @45
    @26
    @50
    cZ
    cA
    @16
    @42
    feq1
    @83
    @18
    @44
    cC
    cM
    @16
    @42
    fveq1
    eqeq1d
    @83
    @25
    @49
    vk
    cZ
    @83
    @22
    @46
    @24
    @48
    @21
    @16
    @42
    fveq1
    @83
    @23
    @47
    @20
    cF
    @20
    @16
    @42
    fveq1
    oveq2d
    eleq12d
    ralbidv
    3anbi123d
    spcev
    syl3anc
    exlimiv
    syl
end
