include "ccnv.mm"
include "cmnf.mm"
include "cioc.mm"
include "co.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "ciin.mm"
include "cin.mm"
include "crest.mm"
include "wss.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "wfn.mm"
include "cr.mm"
include "csalg.mm"
include "adantr.mm"
include "csmblfn.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "smff.mm"
include "ffnd.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "iinss2.mm"
include "syl5ss.mm"
include "ad2antlr.mm"
include "cnvimass.mm"
include "sseli.mm"
include "adantl.mm"
include "wceq.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "nfv.mm"
include "c0.mm"
include "wne.mm"
include "cuz.mm"
include "cz.mm"
include "uzid.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "ne0d.mm"
include "wf.mm"
include "adantlr.mm"
include "sseldd.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "rabeq2i.mm"
include "simprbi.mm"
include "suprclrnmpt.mm"
include "fmptd.mm"
include "fdmd.mm"
include "ad2antrr.mm"
include "eleqtrd.mm"
include "cxr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "rexrd.mm"
include "an32s.mm"
include "syldan.mm"
include "mnfltd.mm"
include "ffdmd.mm"
include "an32.mm"
include "biimpi.mm"
include "suprubrnmpt.mm"
include "fvmpt2d.mm"
include "breqtrrd.mm"
include "simpr.mm"
include "wb.mm"
include "elpreima.mm"
include "mpbid.mm"
include "simprd.mm"
include "iocleubd.mm"
include "letrd.mm"
include "eliocd.mm"
include "elpreimad.mm"
include "ssd.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "sstrd.mm"
include "ralrimiva.mm"
include "ssiin.mm"
include "sylibr.mm"
include "syl5sseq.mm"
include "ssind.mm"
include "iniin1.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "eleq2d.mm"
include "eliind.mm"
include "elinel2.mm"
include "eqeltrd.mm"
include "nfcv.mm"
include "nfii1.mm"
include "nfel.mm"
include "nfan.mm"
include "simpll.mm"
include "eliinid.mm"
include "w3a.mm"
include "elinel1.mm"
include "3ad2ant3.mm"
include "ancoms.mm"
include "3adant1.mm"
include "elind.mm"
include "3adant3.mm"
include "eleqtrrd.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "syld3an3.mm"
include "syl3anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "syldanl.mm"
include "suprleubrnmpt.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "eqsstrd.mm"
include "eqssd.mm"
include "cvv.mm"
include "fvex.mm"
include "dmex.mm"
include "rgenw.mm"
include "iinexd.mm"
include "rabexd.mm"
include "syl5eqel.mm"
include "com.mm"
include "cdom.mm"
include "uzct.mm"
include "saliincl.mm"
include "elrestd.mm"

theorem smfsuplem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  assume smfsuplem1.m: |- ( ph -> M e. ZZ )
  assume smfsuplem1.z: |- Z = ( ZZ>= ` M )
  assume smfsuplem1.s: |- ( ph -> S e. SAlg )
  assume smfsuplem1.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smfsuplem1.d: |- D = { x e. |^|_ n e. Z dom ( F ` n ) | E. y e. RR A. n e. Z ( ( F ` n ) ` x ) <_ y }
  assume smfsuplem1.g: |- G = ( x e. D |-> sup ( ran ( n e. Z |-> ( ( F ` n ) ` x ) ) , RR , < ) )
  assume smfsuplem1.a: |- ( ph -> A e. RR )
  assume smfsuplem1.h: |- ( ph -> H : Z --> S )
  assume smfsuplem1.i: |- ( ( ph /\ n e. Z ) -> ( `' ( F ` n ) " ( -oo (,] A ) ) = ( ( H ` n ) i^i dom ( F ` n ) ) )

  disjoint A n
  disjoint A x
  disjoint n x
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint n y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G n
  disjoint G x
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint M n
  disjoint S n
  disjoint Z n
  disjoint Z x
  disjoint Z y
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( `' G " ( -oo (,] A ) ) e. ( S |`t D ) )

  proof
    wph
    cG
    ccnv
    cmnf
    cA
    cioc
    co
    #
    cima
    #
    vn
    cZ
    vn
    cv
    #
    cH
    cfv
    #
    ciin
    #
    cD
    cin
    #
    cS
    cD
    crest
    co
    wph
    @1
    @5
    wph
    @1
    @4
    cD
    wph
    @1
    @3
    wss
    #
    vn
    cZ
    wral
    @1
    @4
    wss
    wph
    @6
    vn
    cZ
    wph
    @2
    cZ
    wcel
    #
    wa
    #
    @1
    @2
    cF
    cfv
    #
    ccnv
    @0
    cima
    #
    @3
    @8
    vx
    @1
    @10
    @8
    vx
    cv
    #
    @1
    wcel
    #
    wa
    #
    @9
    cdm
    #
    @11
    @0
    @9
    @8
    @9
    @14
    wfn
    #
    @12
    @8
    @14
    cr
    @9
    @8
    @14
    cS
    @9
    wph
    cS
    csalg
    wcel
    @7
    smfsuplem1.s
    adantr
    wph
    cZ
    cS
    csmblfn
    cfv
    @2
    cF
    smfsuplem1.f
    ffvelrnda
    @14
    eqid
    smff
    #
    ffnd
    #
    adantr
    @13
    cD
    @14
    @11
    @7
    cD
    @14
    wss
    wph
    @12
    @7
    cD
    vn
    cZ
    @14
    ciin
    #
    @14
    cD
    @11
    @9
    cfv
    #
    vy
    cv
    cle
    wbr
    vn
    cZ
    wral
    vy
    cr
    wrex
    #
    vx
    @18
    crab
    #
    @18
    smfsuplem1.d
    @20
    vx
    @18
    ssrab2
    eqsstri
    #
    vn
    cZ
    @14
    iinss2
    #
    syl5ss
    ad2antlr
    @13
    @11
    cG
    cdm
    #
    cD
    @12
    @11
    @24
    wcel
    #
    @8
    @1
    @24
    @11
    cG
    @0
    cnvimass
    #
    sseli
    #
    adantl
    wph
    @24
    cD
    wceq
    @7
    @12
    wph
    cD
    cr
    cG
    wph
    vx
    cD
    vn
    cZ
    @19
    cmpt
    crn
    cr
    clt
    csup
    #
    cr
    cG
    wph
    @11
    cD
    wcel
    #
    wa
    #
    vn
    vy
    cZ
    @19
    @30
    vn
    nfv
    #
    wph
    cZ
    c0
    wne
    #
    @29
    wph
    cZ
    cM
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    cM
    @33
    wcel
    smfsuplem1.m
    cM
    uzid
    syl
    smfsuplem1.z
    syl6eleqr
    #
    ne0d
    #
    adantr
    @30
    @7
    wa
    #
    @14
    cr
    @11
    @9
    wph
    @7
    @14
    cr
    @9
    wf
    @29
    @16
    adantlr
    @29
    @7
    @11
    @14
    wcel
    #
    wph
    @29
    @7
    wa
    @18
    @14
    @11
    @7
    @18
    @14
    wss
    @29
    @23
    adantl
    @29
    @11
    @18
    wcel
    #
    @7
    cD
    @18
    @11
    @22
    sseli
    adantr
    sseldd
    #
    adantll
    ffvelrnd
    #
    @29
    @20
    wph
    @29
    @38
    @20
    @20
    vx
    cD
    @18
    smfsuplem1.d
    rabeq2i
    simprbi
    #
    adantl
    #
    suprclrnmpt
    #
    smfsuplem1.g
    fmptd
    #
    fdmd
    #
    ad2antrr
    eleqtrd
    #
    sseldd
    @13
    cmnf
    cA
    @19
    cmnf
    cxr
    wcel
    #
    @13
    mnfxr
    a1i
    wph
    cA
    cxr
    wcel
    #
    @7
    @12
    wph
    cA
    smfsuplem1.a
    rexrd
    #
    ad2antrr
    @13
    @19
    @8
    @12
    @29
    @19
    cr
    wcel
    #
    @46
    wph
    @29
    @7
    @50
    @40
    an32s
    syldan
    #
    rexrd
    @13
    @19
    @51
    mnfltd
    @13
    @19
    @11
    cG
    cfv
    #
    cA
    @51
    wph
    @12
    @52
    cr
    wcel
    #
    @7
    wph
    @12
    @25
    @53
    @12
    @25
    wph
    @27
    adantl
    wph
    @24
    cr
    @11
    cG
    wph
    cD
    cr
    cG
    @44
    ffdmd
    ffvelrnda
    syldan
    adantlr
    wph
    cA
    cr
    wcel
    #
    @7
    @12
    smfsuplem1.a
    ad2antrr
    @8
    @12
    @29
    @19
    @52
    cle
    wbr
    @46
    @8
    @29
    wa
    #
    @19
    @28
    @52
    cle
    @55
    @36
    @19
    @28
    cle
    wbr
    @55
    @36
    wph
    @7
    @29
    an32
    biimpi
    @30
    vn
    vy
    cZ
    @19
    @31
    @40
    @42
    suprubrnmpt
    syl
    wph
    @29
    @52
    @28
    wceq
    #
    @7
    wph
    vx
    cD
    @28
    cG
    cr
    cG
    vx
    cD
    @28
    cmpt
    wceq
    wph
    smfsuplem1.g
    a1i
    @43
    fvmpt2d
    #
    adantlr
    breqtrrd
    syldan
    wph
    @12
    @52
    cA
    cle
    wbr
    @7
    wph
    @12
    wa
    #
    cmnf
    cA
    @52
    @47
    @58
    mnfxr
    a1i
    wph
    @48
    @12
    @49
    adantr
    @58
    @29
    @52
    @0
    wcel
    #
    @58
    @12
    @29
    @59
    wa
    #
    wph
    @12
    simpr
    wph
    @12
    @60
    wb
    #
    @12
    wph
    cG
    cD
    wfn
    #
    @61
    wph
    cD
    cr
    cG
    @44
    ffnd
    #
    cD
    @11
    @0
    cG
    elpreima
    syl
    adantr
    mpbid
    simprd
    iocleubd
    adantlr
    letrd
    eliocd
    elpreimad
    ssd
    @8
    @10
    @3
    @14
    cin
    #
    @3
    smfsuplem1.i
    @3
    @14
    inss1
    syl6eqss
    sstrd
    ralrimiva
    vn
    cZ
    @3
    @1
    ssiin
    sylibr
    wph
    @24
    @1
    cD
    @26
    @45
    syl5sseq
    ssind
    wph
    @5
    vn
    cZ
    @3
    cD
    cin
    #
    ciin
    #
    @1
    wph
    @32
    @5
    @66
    wceq
    @35
    vn
    cZ
    cD
    @3
    iniin1
    syl
    wph
    vx
    @66
    @1
    wph
    @11
    @66
    wcel
    #
    wa
    #
    cD
    @11
    @0
    cG
    wph
    @62
    @67
    @63
    adantr
    @68
    @11
    cM
    cH
    cfv
    #
    cD
    cin
    #
    wcel
    #
    @29
    @68
    vn
    @11
    cZ
    @65
    @70
    cM
    wph
    @67
    simpr
    wph
    cM
    cZ
    wcel
    @67
    @34
    adantr
    @2
    cM
    wceq
    #
    @65
    @70
    @11
    @72
    @3
    @69
    cD
    @2
    cM
    cH
    fveq2
    ineq1d
    eleq2d
    eliind
    #
    @11
    @69
    cD
    elinel2
    #
    syl
    #
    @68
    cmnf
    cA
    @52
    @47
    @68
    mnfxr
    a1i
    wph
    @48
    @67
    @49
    adantr
    wph
    @67
    @29
    @52
    cxr
    wcel
    @75
    @30
    @52
    @30
    @52
    @28
    cr
    @57
    @43
    eqeltrd
    #
    rexrd
    syldan
    wph
    @67
    @71
    cmnf
    @52
    clt
    wbr
    @73
    wph
    @71
    wa
    @52
    wph
    @71
    @29
    @53
    @71
    @29
    wph
    @74
    adantl
    @76
    syldan
    mnfltd
    syldan
    @68
    @52
    @28
    cA
    cle
    wph
    @67
    @29
    @56
    @75
    @57
    syldan
    @68
    @28
    cA
    cle
    wbr
    @19
    cA
    cle
    wbr
    #
    vn
    cZ
    wral
    @68
    @77
    vn
    cZ
    wph
    @67
    vn
    wph
    vn
    nfv
    vn
    @11
    @66
    vn
    @11
    nfcv
    vn
    cZ
    @65
    nfii1
    nfel
    nfan
    #
    @68
    @7
    @77
    @68
    @7
    wa
    wph
    @7
    @11
    @65
    wcel
    #
    @77
    wph
    @67
    @7
    simpll
    @68
    @7
    simpr
    @67
    @7
    @79
    wph
    vn
    @11
    cZ
    @65
    eliinid
    adantll
    wph
    @7
    @79
    @11
    @10
    wcel
    #
    @77
    wph
    @7
    @79
    w3a
    #
    @11
    @64
    @10
    @81
    @3
    @14
    @11
    @79
    wph
    @11
    @3
    wcel
    @7
    @11
    @3
    cD
    elinel1
    3ad2ant3
    @7
    @79
    @37
    wph
    @7
    @79
    @29
    @37
    @79
    @29
    @7
    @11
    @3
    cD
    elinel2
    adantl
    @29
    @7
    @37
    @39
    ancoms
    syldan
    3adant1
    elind
    wph
    @7
    @10
    @64
    wceq
    @79
    smfsuplem1.i
    3adant3
    eleqtrrd
    wph
    @7
    @80
    w3a
    #
    cmnf
    cA
    @19
    @47
    @82
    mnfxr
    a1i
    wph
    @7
    @48
    @80
    @49
    3ad2ant1
    @82
    @37
    @19
    @0
    wcel
    #
    @82
    @80
    @37
    @83
    wa
    #
    wph
    @7
    @80
    simp3
    wph
    @7
    @80
    @84
    wb
    #
    @80
    @8
    @15
    @85
    @17
    @14
    @11
    @0
    @9
    elpreima
    syl
    3adant3
    mpbid
    simprd
    iocleubd
    syld3an3
    syl3anc
    ex
    ralrimi
    @68
    vn
    vy
    cZ
    @19
    cA
    @78
    wph
    @32
    @67
    @35
    adantr
    wph
    @67
    @29
    @7
    @50
    @75
    @40
    syldanl
    @68
    @29
    @20
    @75
    @41
    syl
    wph
    @54
    @67
    smfsuplem1.a
    adantr
    suprleubrnmpt
    mpbird
    eqbrtrd
    eliocd
    elpreimad
    ssd
    eqsstrd
    eqssd
    wph
    @5
    cD
    cS
    csalg
    cvv
    @4
    smfsuplem1.s
    wph
    cD
    @21
    cvv
    smfsuplem1.d
    wph
    @20
    vx
    @18
    @21
    cvv
    @21
    eqid
    wph
    vn
    cZ
    @14
    cvv
    @35
    @14
    cvv
    wcel
    #
    vn
    cZ
    wral
    wph
    @86
    vn
    cZ
    @9
    @2
    cF
    fvex
    dmex
    rgenw
    a1i
    iinexd
    rabexd
    syl5eqel
    wph
    cS
    vn
    @3
    cZ
    smfsuplem1.s
    cZ
    com
    cdom
    wbr
    wph
    cM
    cZ
    smfsuplem1.z
    uzct
    a1i
    @35
    wph
    cZ
    cS
    @2
    cH
    smfsuplem1.h
    ffvelrnda
    saliincl
    @5
    eqid
    elrestd
    eqeltrd
end
