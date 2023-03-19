include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "cmpt.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "cr.mm"
include "wi.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfel1.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "simpr.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "chvar.mm"
include "cneg.mm"
include "negeq.mm"
include "fveq2d.mm"
include "negeqd.mm"
include "eqeq12d.mm"
include "znegcl.mm"
include "adantl.mm"
include "negex.mm"
include "vtocl.mm"
include "sylan2.mm"
include "fvmptg.mm"
include "chvarv.mm"
include "3eqtr4d.mm"
include "cn0.mm"
include "nfcv.mm"
include "nfbr.mm"
include "3anbi2d.mm"
include "breq1.mm"
include "breq1d.mm"
include "3anbi3d.mm"
include "breq2.mm"
include "breq2d.mm"
include "nn0z.mm"
include "3adant3.mm"
include "nfeq1.mm"
include "3adant2.mm"
include "breq12d.mm"
include "sylibrd.mm"
include "monotoddzzfi.mm"
include "simp2.mm"
include "vtoclg.mm"
include "anabsi7.mm"
include "simp3.mm"
include "bitrd.mm"

theorem monotoddzz
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  assume monotoddzz.1: |- ( ( ph /\ x e. NN0 /\ y e. NN0 ) -> ( x < y -> E < F ) )
  assume monotoddzz.2: |- ( ( ph /\ x e. ZZ ) -> E e. RR )
  assume monotoddzz.3: |- ( ( ph /\ y e. ZZ ) -> G = -u F )
  assume monotoddzz.4: |- ( x = A -> E = C )
  assume monotoddzz.5: |- ( x = B -> E = D )
  assume monotoddzz.6: |- ( x = y -> E = F )
  assume monotoddzz.7: |- ( x = -u y -> E = G )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint E y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint G x
  disjoint a ph
  disjoint b ph
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint E a
  disjoint E b
  disjoint C a
  disjoint C b
  disjoint D a
  disjoint D b
  disjoint F a
  disjoint F b
  disjoint G a
  disjoint G b
  assert |- ( ( ph /\ A e. ZZ /\ B e. ZZ ) -> ( A < B <-> C < D ) )

  proof
    wph
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    cA
    vx
    cz
    cE
    cmpt
    #
    cfv
    #
    cB
    @3
    cfv
    #
    clt
    wbr
    cC
    cD
    clt
    wbr
    wph
    va
    vb
    cA
    cB
    @3
    wph
    vx
    cv
    #
    cz
    wcel
    #
    wa
    #
    @6
    @3
    cfv
    #
    cr
    wcel
    #
    wi
    wph
    va
    cv
    #
    cz
    wcel
    #
    wa
    #
    @11
    @3
    cfv
    #
    cr
    wcel
    #
    wi
    vx
    va
    @13
    @15
    vx
    @13
    vx
    nfv
    vx
    @14
    cr
    vx
    cz
    cE
    @11
    nffvmpt1
    #
    nfel1
    nfim
    @6
    @11
    wceq
    #
    @8
    @13
    @10
    @15
    @17
    @7
    @12
    wph
    @6
    @11
    cz
    eleq1
    anbi2d
    @17
    @9
    @14
    cr
    @6
    @11
    @3
    fveq2
    #
    eleq1d
    imbi12d
    @8
    @9
    cE
    cr
    @8
    @7
    cE
    cr
    wcel
    #
    @9
    cE
    wceq
    #
    wph
    @7
    simpr
    monotoddzz.2
    vx
    cz
    cE
    cr
    @3
    @3
    eqid
    #
    fvmpt2
    syl2anc
    #
    monotoddzz.2
    eqeltrd
    chvar
    wph
    vy
    cv
    #
    cz
    wcel
    #
    wa
    #
    @23
    cneg
    #
    @3
    cfv
    #
    @23
    @3
    cfv
    #
    cneg
    #
    wceq
    #
    wi
    @13
    @11
    cneg
    #
    @3
    cfv
    #
    @14
    cneg
    #
    wceq
    #
    wi
    vy
    va
    @23
    @11
    wceq
    #
    @25
    @13
    @30
    @34
    @35
    @24
    @12
    wph
    @23
    @11
    cz
    eleq1
    anbi2d
    @35
    @27
    @32
    @29
    @33
    @35
    @26
    @31
    @3
    @23
    @11
    negeq
    fveq2d
    @35
    @28
    @14
    @23
    @11
    @3
    fveq2
    negeqd
    eqeq12d
    imbi12d
    @25
    cG
    cF
    cneg
    @27
    @29
    monotoddzz.3
    @25
    @26
    cz
    wcel
    #
    cG
    cr
    wcel
    #
    @27
    cG
    wceq
    @24
    @36
    wph
    @23
    znegcl
    #
    adantl
    @24
    wph
    @36
    @37
    @38
    @8
    @19
    wi
    #
    wph
    @36
    wa
    #
    @37
    wi
    vx
    @26
    @23
    negex
    @6
    @26
    wceq
    #
    @8
    @40
    @19
    @37
    @41
    @7
    @36
    wph
    @6
    @26
    cz
    eleq1
    anbi2d
    @41
    cE
    cG
    cr
    monotoddzz.7
    eleq1d
    imbi12d
    monotoddzz.2
    vtocl
    sylan2
    vx
    @26
    cE
    cG
    cz
    cr
    @3
    monotoddzz.7
    @21
    fvmptg
    syl2anc
    @25
    @28
    cF
    @25
    @24
    cF
    cr
    wcel
    #
    @28
    cF
    wceq
    #
    wph
    @24
    simpr
    @39
    @25
    @42
    wi
    vx
    vy
    @6
    @23
    wceq
    #
    @8
    @25
    @19
    @42
    @44
    @7
    @24
    wph
    @6
    @23
    cz
    eleq1
    anbi2d
    @44
    cE
    cF
    cr
    monotoddzz.6
    eleq1d
    imbi12d
    monotoddzz.2
    chvarv
    vx
    @23
    cE
    cF
    cz
    cr
    @3
    monotoddzz.6
    @21
    fvmptg
    syl2anc
    negeqd
    3eqtr4d
    chvarv
    wph
    @6
    cn0
    wcel
    #
    vb
    cv
    #
    cn0
    wcel
    #
    w3a
    #
    @6
    @46
    clt
    wbr
    #
    @9
    @46
    @3
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wi
    #
    wph
    @11
    cn0
    wcel
    #
    @47
    w3a
    #
    @11
    @46
    clt
    wbr
    #
    @14
    @50
    clt
    wbr
    #
    wi
    #
    wi
    vx
    va
    @55
    @58
    vx
    @55
    vx
    nfv
    @56
    @57
    vx
    @56
    vx
    nfv
    vx
    @14
    @50
    clt
    @16
    vx
    clt
    nfcv
    vx
    cz
    cE
    @46
    nffvmpt1
    nfbr
    nfim
    nfim
    @17
    @48
    @55
    @52
    @58
    @17
    @45
    @54
    wph
    @47
    @6
    @11
    cn0
    eleq1
    3anbi2d
    @17
    @49
    @56
    @51
    @57
    @6
    @11
    @46
    clt
    breq1
    @17
    @9
    @14
    @50
    clt
    @18
    breq1d
    imbi12d
    imbi12d
    wph
    @45
    @23
    cn0
    wcel
    #
    w3a
    #
    @6
    @23
    clt
    wbr
    #
    @9
    @28
    clt
    wbr
    #
    wi
    #
    wi
    @53
    vy
    vb
    @23
    @46
    wceq
    #
    @60
    @48
    @63
    @52
    @64
    @59
    @47
    wph
    @45
    @23
    @46
    cn0
    eleq1
    3anbi3d
    @64
    @61
    @49
    @62
    @51
    @23
    @46
    @6
    clt
    breq2
    @64
    @28
    @50
    @9
    clt
    @23
    @46
    @3
    fveq2
    breq2d
    imbi12d
    imbi12d
    @60
    @61
    cE
    cF
    clt
    wbr
    @62
    monotoddzz.1
    @60
    @9
    cE
    @28
    cF
    clt
    wph
    @45
    @20
    @59
    @45
    wph
    @7
    @20
    @6
    nn0z
    @22
    sylan2
    #
    3adant3
    wph
    @59
    @43
    @45
    wph
    @45
    wa
    #
    @20
    wi
    wph
    @59
    wa
    #
    @43
    wi
    vx
    vy
    @67
    @43
    vx
    @67
    vx
    nfv
    vx
    @28
    cF
    vx
    cz
    cE
    @23
    nffvmpt1
    nfeq1
    nfim
    @44
    @66
    @67
    @20
    @43
    @44
    @45
    @59
    wph
    @6
    @23
    cn0
    eleq1
    anbi2d
    @44
    @9
    @28
    cE
    cF
    @6
    @23
    @3
    fveq2
    monotoddzz.6
    eqeq12d
    imbi12d
    @65
    chvar
    3adant2
    breq12d
    sylibrd
    chvarv
    chvar
    monotoddzzfi
    @2
    @4
    cC
    @5
    cD
    clt
    @2
    @0
    cC
    cr
    wcel
    #
    @4
    cC
    wceq
    wph
    @0
    @1
    simp2
    wph
    @0
    @68
    @1
    wph
    @0
    @68
    @39
    wph
    @0
    wa
    #
    @68
    wi
    vx
    cA
    cz
    @6
    cA
    wceq
    #
    @8
    @69
    @19
    @68
    @70
    @7
    @0
    wph
    @6
    cA
    cz
    eleq1
    anbi2d
    @70
    cE
    cC
    cr
    monotoddzz.4
    eleq1d
    imbi12d
    monotoddzz.2
    vtoclg
    anabsi7
    3adant3
    vx
    cA
    cE
    cC
    cz
    cr
    @3
    monotoddzz.4
    @21
    fvmptg
    syl2anc
    @2
    @1
    cD
    cr
    wcel
    #
    @5
    cD
    wceq
    wph
    @0
    @1
    simp3
    wph
    @1
    @71
    @0
    wph
    @1
    @71
    @39
    wph
    @1
    wa
    #
    @71
    wi
    vx
    cB
    cz
    @6
    cB
    wceq
    #
    @8
    @72
    @19
    @71
    @73
    @7
    @1
    wph
    @6
    cB
    cz
    eleq1
    anbi2d
    @73
    cE
    cD
    cr
    monotoddzz.5
    eleq1d
    imbi12d
    monotoddzz.2
    vtoclg
    anabsi7
    3adant2
    vx
    cB
    cE
    cD
    cz
    cr
    @3
    monotoddzz.5
    @21
    fvmptg
    syl2anc
    breq12d
    bitrd
end
