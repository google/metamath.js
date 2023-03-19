include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cuni.mm"
include "wceq.mm"
include "c0.mm"
include "crn.mm"
include "cif.mm"
include "csn.mm"
include "cun.mm"
include "cmpt.mm"
include "cima.mm"
include "tfr2.mm"
include "adantl.mm"
include "eqidd.mm"
include "simpr.mm"
include "dmeqd.mm"
include "wfn.mm"
include "wss.mm"
include "tfr1.mm"
include "onss.mm"
include "ad2antlr.mm"
include "fnssres.mm"
include "sylancr.mm"
include "fndm.mm"
include "syl.mm"
include "eqtrd.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "eqeq1d.mm"
include "rneqd.mm"
include "df-ima.mm"
include "syl6eqr.mm"
include "ifbieq2d.mm"
include "fveq12d.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "eleq1d.mm"
include "ifbieq12d.mm"
include "wn.mm"
include "csuc.mm"
include "onuni.mm"
include "ad3antlr.mm"
include "sucidg.mm"
include "word.mm"
include "wo.mm"
include "eloni.mm"
include "orduniorsuc.mm"
include "orcanai.mm"
include "eleqtrrd.mm"
include "fvres.mm"
include "uneq1d.mm"
include "ifbid.mm"
include "ifeq2da.mm"
include "wfun.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "resfunexg.mm"
include "elex.mm"
include "funimaexg.mm"
include "mpan.mm"
include "uniexg.mm"
include "ifcl.mm"
include "syl2an.mm"
include "fvex.mm"
include "snex.mm"
include "0ex.mm"
include "ifex.mm"
include "unex.mm"
include "sylancl.mm"
include "fvmptd.mm"

theorem ttukeylem3
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let va: setvar a
  let vy: setvar y
  let cD: class D
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
  disjoint D x
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
  assert |- ( ( ph /\ C e. On ) -> ( G ` C ) = if ( C = U. C , if ( C = (/) , B , U. ( G " C ) ) , ( ( G ` U. C ) u. if ( ( ( G ` U. C ) u. { ( F ` U. C ) } ) e. A , { ( F ` U. C ) } , (/) ) ) ) )

  proof
    wph
    cC
    con0
    wcel
    #
    wa
    #
    cC
    cG
    cfv
    #
    cG
    cC
    cres
    #
    vz
    cvv
    vz
    cv
    #
    cdm
    #
    @5
    cuni
    #
    wceq
    #
    @5
    c0
    wceq
    #
    cB
    @4
    crn
    #
    cuni
    #
    cif
    #
    @6
    @4
    cfv
    #
    @12
    @6
    cF
    cfv
    #
    csn
    #
    cun
    #
    cA
    wcel
    #
    @14
    c0
    cif
    #
    cun
    #
    cif
    #
    cmpt
    #
    cfv
    #
    cC
    cC
    cuni
    #
    wceq
    #
    cC
    c0
    wceq
    #
    cB
    cG
    cC
    cima
    #
    cuni
    #
    cif
    #
    @22
    cG
    cfv
    #
    @28
    @22
    cF
    cfv
    #
    csn
    #
    cun
    #
    cA
    wcel
    #
    @30
    c0
    cif
    #
    cun
    #
    cif
    #
    @0
    @2
    @21
    wceq
    wph
    cC
    cG
    @20
    ttukeylem.4
    tfr2
    adantl
    @1
    vz
    @3
    @19
    @35
    cvv
    @20
    cvv
    @1
    @20
    eqidd
    @1
    @4
    @3
    wceq
    #
    wa
    #
    @19
    @23
    @27
    @22
    @3
    cfv
    #
    @38
    @30
    cun
    #
    cA
    wcel
    #
    @30
    c0
    cif
    #
    cun
    #
    cif
    @35
    @37
    @7
    @23
    @11
    @18
    @27
    @42
    @37
    @5
    cC
    @6
    @22
    @37
    @5
    @3
    cdm
    #
    cC
    @37
    @4
    @3
    @1
    @36
    simpr
    #
    dmeqd
    @37
    @3
    cC
    wfn
    #
    @43
    cC
    wceq
    @37
    cG
    con0
    wfn
    #
    cC
    con0
    wss
    #
    @45
    cG
    @20
    ttukeylem.4
    tfr1
    #
    @0
    @47
    wph
    @36
    cC
    onss
    ad2antlr
    con0
    cC
    cG
    fnssres
    sylancr
    cC
    @3
    fndm
    syl
    eqtrd
    #
    @37
    @5
    cC
    @49
    unieqd
    #
    eqeq12d
    @37
    @8
    @24
    @10
    @26
    cB
    @37
    @5
    cC
    c0
    @49
    eqeq1d
    @37
    @9
    @25
    @37
    @9
    @3
    crn
    @25
    @37
    @4
    @3
    @44
    rneqd
    cG
    cC
    df-ima
    syl6eqr
    unieqd
    ifbieq2d
    @37
    @12
    @38
    @17
    @41
    @37
    @6
    @22
    @4
    @3
    @44
    @50
    fveq12d
    #
    @37
    @16
    @40
    @14
    c0
    @30
    c0
    @37
    @15
    @39
    cA
    @37
    @12
    @38
    @14
    @30
    @51
    @37
    @13
    @29
    @37
    @6
    @22
    cF
    @50
    fveq2d
    sneqd
    #
    uneq12d
    eleq1d
    @52
    @37
    c0
    eqidd
    ifbieq12d
    uneq12d
    ifbieq12d
    @37
    @23
    @42
    @34
    @27
    @37
    @23
    wn
    #
    wa
    #
    @38
    @28
    @41
    @33
    @54
    @22
    cC
    wcel
    @38
    @28
    wceq
    @54
    @22
    @22
    csuc
    #
    cC
    @54
    @22
    con0
    wcel
    #
    @22
    @55
    wcel
    @0
    @56
    wph
    @36
    @53
    cC
    onuni
    ad3antlr
    @22
    con0
    sucidg
    syl
    @37
    @23
    cC
    @55
    wceq
    #
    @37
    cC
    word
    #
    @23
    @57
    wo
    @0
    @58
    wph
    @36
    cC
    eloni
    ad2antlr
    cC
    orduniorsuc
    syl
    orcanai
    eleqtrrd
    @22
    cC
    cG
    fvres
    syl
    #
    @54
    @40
    @32
    @30
    c0
    @54
    @39
    @31
    cA
    @54
    @38
    @28
    @30
    @59
    uneq1d
    eleq1d
    ifbid
    uneq12d
    ifeq2da
    eqtrd
    @1
    cG
    wfun
    #
    @0
    @3
    cvv
    wcel
    @46
    @60
    @48
    con0
    cG
    fnfun
    ax-mp
    #
    wph
    @0
    simpr
    cG
    cC
    con0
    resfunexg
    sylancr
    @1
    @27
    cvv
    wcel
    #
    @34
    cvv
    wcel
    @35
    cvv
    wcel
    wph
    cB
    cvv
    wcel
    #
    @26
    cvv
    wcel
    #
    @62
    @0
    wph
    cB
    cA
    wcel
    @63
    ttukeylem.2
    cB
    cA
    elex
    syl
    @0
    @25
    cvv
    wcel
    #
    @64
    @60
    @0
    @65
    @61
    cG
    cC
    con0
    funimaexg
    mpan
    @25
    cvv
    uniexg
    syl
    @24
    cB
    @26
    cvv
    ifcl
    syl2an
    @28
    @33
    @22
    cG
    fvex
    @32
    @30
    c0
    @29
    snex
    0ex
    ifex
    unex
    @23
    @27
    @34
    cvv
    ifcl
    sylancl
    fvmptd
    eqtrd
end
