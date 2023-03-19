include "con0.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "sseq2.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wral.mm"
include "r19.21v.mm"
include "wo.mm"
include "wb.mm"
include "simpllr.mm"
include "simplr.mm"
include "onsseleq.mm"
include "syl2anc.mm"
include "cuni.mm"
include "c0.mm"
include "cima.mm"
include "cif.mm"
include "csn.mm"
include "cun.mm"
include "wfn.mm"
include "cvv.mm"
include "cdm.mm"
include "crn.mm"
include "cmpt.mm"
include "tfr1.mm"
include "a1i.mm"
include "onss.mm"
include "syl.mm"
include "simprr.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "elssuni.mm"
include "wn.mm"
include "n0i.mm"
include "iffalse.mm"
include "3syl.mm"
include "sseqtr4d.mm"
include "adantr.mm"
include "csuc.mm"
include "vuniex.mm"
include "sucid.mm"
include "word.mm"
include "eloni.mm"
include "orduniorsuc.mm"
include "orcanai.mm"
include "syl5eleqr.mm"
include "simplrl.mm"
include "rspcv.mm"
include "syl3c.mm"
include "ssun1.mm"
include "syl6ss.mm"
include "ifbothda.mm"
include "simplll.mm"
include "ttukeylem3.mm"
include "expr.mm"
include "eqimss.mm"
include "jaod.mm"
include "sylbid.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "syl5bi.mm"
include "tfis3.mm"
include "expdcom.mm"
include "3imp2.mm"

theorem ttukeylem5
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let va: setvar a
  let vy: setvar y
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume ttukeylem.1: |- ( ph -> F : ( card ` ( U. A \ B ) ) -1-1-onto-> ( U. A \ B ) )
  assume ttukeylem.2: |- ( ph -> B e. A )
  assume ttukeylem.3: |- ( ph -> A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) )
  assume ttukeylem.4: |- G = recs ( ( z e. _V |-> if ( dom z = U. dom z , if ( dom z = (/) , B , U. ran z ) , ( ( z ` U. dom z ) u. if ( ( ( z ` U. dom z ) u. { ( F ` U. dom z ) } ) e. A , { ( F ` U. dom z ) } , (/) ) ) ) ) )

  disjoint x z
  disjoint C x
  disjoint C z
  disjoint D x
  disjoint G x
  disjoint G z
  disjoint ph z
  disjoint A x
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint F x
  disjoint F z
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint x y
  disjoint y z
  disjoint C y
  disjoint D y
  disjoint a f
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint G a
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G y
  disjoint a ph
  disjoint f ph
  disjoint ph u
  disjoint ph w
  disjoint ph y
  disjoint A a
  disjoint A f
  disjoint A u
  disjoint A w
  disjoint A y
  disjoint B a
  disjoint B f
  disjoint B u
  disjoint B w
  disjoint B y
  assert |- ( ( ph /\ ( C e. On /\ D e. On /\ C C_ D ) ) -> ( G ` C ) C_ ( G ` D ) )

  proof
    wph
    cC
    con0
    wcel
    #
    cD
    con0
    wcel
    #
    cC
    cD
    wss
    #
    cC
    cG
    cfv
    #
    cD
    cG
    cfv
    #
    wss
    #
    @1
    wph
    @0
    @2
    @5
    wi
    #
    wph
    @0
    wa
    #
    cC
    vy
    cv
    #
    wss
    #
    @3
    @8
    cG
    cfv
    #
    wss
    #
    wi
    #
    wi
    #
    @7
    cC
    va
    cv
    #
    wss
    #
    @3
    @14
    cG
    cfv
    #
    wss
    #
    wi
    #
    wi
    #
    @7
    @6
    wi
    vy
    va
    cD
    @8
    @14
    wceq
    #
    @12
    @18
    @7
    @20
    @9
    @15
    @11
    @17
    @8
    @14
    cC
    sseq2
    @20
    @10
    @16
    @3
    @8
    @14
    cG
    fveq2
    sseq2d
    imbi12d
    imbi2d
    @8
    cD
    wceq
    #
    @12
    @6
    @7
    @21
    @9
    @2
    @11
    @5
    @8
    cD
    cC
    sseq2
    @21
    @10
    @4
    @3
    @8
    cD
    cG
    fveq2
    sseq2d
    imbi12d
    imbi2d
    @19
    va
    @8
    wral
    @7
    @18
    va
    @8
    wral
    #
    wi
    @8
    con0
    wcel
    #
    @13
    @7
    @18
    va
    @8
    r19.21v
    @23
    @7
    @22
    @12
    @7
    @23
    @22
    @12
    wi
    @7
    @23
    wa
    #
    @22
    @12
    @24
    @22
    wa
    #
    @9
    cC
    @8
    wcel
    #
    cC
    @8
    wceq
    #
    wo
    #
    @11
    @25
    @0
    @23
    @9
    @28
    wb
    wph
    @0
    @23
    @22
    simpllr
    @7
    @23
    @22
    simplr
    cC
    @8
    onsseleq
    syl2anc
    @25
    @26
    @11
    @27
    @24
    @22
    @26
    @11
    @24
    @22
    @26
    wa
    #
    wa
    #
    @3
    @8
    @8
    cuni
    #
    wceq
    #
    @8
    c0
    wceq
    #
    cB
    cG
    @8
    cima
    #
    cuni
    #
    cif
    #
    @31
    cG
    cfv
    #
    @37
    @31
    cF
    cfv
    csn
    #
    cun
    cA
    wcel
    @38
    c0
    cif
    #
    cun
    #
    cif
    #
    @10
    @32
    @3
    @36
    wss
    #
    @3
    @40
    wss
    @3
    @41
    wss
    @30
    @36
    @40
    @36
    @41
    @3
    sseq2
    @40
    @41
    @3
    sseq2
    @30
    @42
    @32
    @30
    @3
    @35
    @36
    @30
    @3
    @34
    wcel
    #
    @3
    @35
    wss
    @30
    cG
    con0
    wfn
    #
    @8
    con0
    wss
    #
    @26
    @43
    @44
    @30
    cG
    vz
    cvv
    vz
    cv
    #
    cdm
    #
    @47
    cuni
    #
    wceq
    @47
    c0
    wceq
    cB
    @46
    crn
    cuni
    cif
    @48
    @46
    cfv
    #
    @49
    @48
    cF
    cfv
    csn
    #
    cun
    cA
    wcel
    @50
    c0
    cif
    cun
    cif
    cmpt
    ttukeylem.4
    tfr1
    a1i
    @30
    @23
    @45
    @7
    @23
    @29
    simplr
    #
    @8
    onss
    syl
    @24
    @22
    @26
    simprr
    #
    con0
    @8
    cG
    cC
    fnfvima
    syl3anc
    @3
    @34
    elssuni
    syl
    @30
    @26
    @33
    wn
    @36
    @35
    wceq
    @52
    @8
    cC
    n0i
    @33
    cB
    @35
    iffalse
    3syl
    sseqtr4d
    adantr
    @30
    @32
    wn
    #
    wa
    #
    @3
    @37
    @40
    @54
    @31
    @8
    wcel
    @22
    cC
    @31
    wss
    #
    @3
    @37
    wss
    #
    @54
    @31
    @31
    csuc
    #
    @8
    @31
    vy
    vuniex
    sucid
    @30
    @32
    @8
    @57
    wceq
    #
    @30
    @23
    @8
    word
    @32
    @58
    wo
    @51
    @8
    eloni
    @8
    orduniorsuc
    3syl
    orcanai
    syl5eleqr
    @24
    @22
    @26
    @53
    simplrl
    @54
    @26
    @55
    @30
    @26
    @53
    @52
    adantr
    cC
    @8
    elssuni
    syl
    @18
    @55
    @56
    wi
    va
    @31
    @8
    @14
    @31
    wceq
    #
    @15
    @55
    @17
    @56
    @14
    @31
    cC
    sseq2
    @59
    @16
    @37
    @3
    @14
    @31
    cG
    fveq2
    sseq2d
    imbi12d
    rspcv
    syl3c
    @37
    @39
    ssun1
    syl6ss
    ifbothda
    @30
    wph
    @23
    @10
    @41
    wceq
    wph
    @0
    @23
    @29
    simplll
    @51
    wph
    vx
    vz
    cA
    cB
    @8
    cF
    cG
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem.4
    ttukeylem3
    syl2anc
    sseqtr4d
    expr
    @27
    @11
    wi
    @25
    @27
    @3
    @10
    wceq
    @11
    cC
    @8
    cG
    fveq2
    @3
    @10
    eqimss
    syl
    a1i
    jaod
    sylbid
    ex
    expcom
    a2d
    syl5bi
    tfis3
    expdcom
    3imp2
end
