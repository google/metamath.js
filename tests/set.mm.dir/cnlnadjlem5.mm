include "chil.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "nfcv.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfov.mm"
include "nfeq2.mm"
include "nfral.mm"
include "oveq2.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "crab.mm"
include "cvv.mm"
include "crio.mm"
include "riotaex.mm"
include "eqeltri.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "wb.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "cbvralv.mm"
include "a1i.mm"
include "cnlnadjlem1.mm"
include "eqeq1d.mm"
include "ralbiia.mm"
include "syl6bbr.mm"
include "riotabiia.mm"
include "eqtri.mm"
include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "wreu.mm"
include "wa.mm"
include "cnlnadjlem2.mm"
include "elin.mm"
include "sylibr.mm"
include "riesz4.mm"
include "riotacl2.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "eqeltrd.mm"
include "eqeq2d.mm"
include "syl5bb.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl.mm"
include "vtoclgaf.mm"
include "rspccva.mm"
include "sylan.mm"

theorem cnlnadjlem5
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vz: setvar z
  let vt: setvar t
  let vx: setvar x
  assume cnlnadjlem.1: |- T e. LinOp
  assume cnlnadjlem.2: |- T e. ContOp
  assume cnlnadjlem.3: |- G = ( g e. ~H |-> ( ( T ` g ) .ih y ) )
  assume cnlnadjlem.4: |- B = ( iota_ w e. ~H A. v e. ~H ( ( T ` v ) .ih y ) = ( v .ih w ) )
  assume cnlnadjlem.5: |- F = ( y e. ~H |-> B )

  disjoint g v
  disjoint g w
  disjoint g y
  disjoint A g
  disjoint v w
  disjoint v y
  disjoint A v
  disjoint w y
  disjoint A w
  disjoint A y
  disjoint F w
  disjoint T g
  disjoint T v
  disjoint T w
  disjoint T y
  disjoint G v
  disjoint G w
  disjoint f g
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g z
  disjoint v z
  disjoint w z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint f t
  disjoint f x
  disjoint F f
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint F t
  disjoint w x
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint T f
  disjoint g t
  disjoint g x
  disjoint t v
  disjoint t y
  disjoint T t
  disjoint v x
  disjoint x y
  disjoint T x
  disjoint T z
  disjoint C f
  disjoint G f
  disjoint G x
  disjoint G z
  assert |- ( ( A e. ~H /\ C e. ~H ) -> ( ( T ` C ) .ih A ) = ( C .ih ( F ` A ) ) )

  proof
    cA
    chil
    wcel
    vf
    cv
    #
    cT
    cfv
    #
    cA
    csp
    co
    #
    @0
    cA
    cF
    cfv
    #
    csp
    co
    #
    wceq
    #
    vf
    chil
    wral
    #
    cC
    chil
    wcel
    cC
    cT
    cfv
    #
    cA
    csp
    co
    #
    cC
    @3
    csp
    co
    #
    wceq
    #
    @1
    vy
    cv
    #
    csp
    co
    #
    @0
    @11
    cF
    cfv
    #
    csp
    co
    #
    wceq
    #
    vf
    chil
    wral
    #
    @6
    vy
    cA
    chil
    vy
    cA
    nfcv
    #
    @5
    vy
    vf
    chil
    vy
    chil
    nfcv
    vy
    @2
    @4
    vy
    @0
    @3
    csp
    vy
    @0
    nfcv
    vy
    csp
    nfcv
    vy
    cA
    cF
    vy
    cF
    vy
    chil
    cB
    cmpt
    cnlnadjlem.5
    vy
    chil
    cB
    nfmpt1
    nfcxfr
    @17
    nffv
    nfov
    nfeq2
    nfral
    @11
    cA
    wceq
    #
    @15
    @5
    vf
    chil
    @18
    @12
    @2
    @14
    @4
    @11
    cA
    @1
    csp
    oveq2
    @18
    @13
    @3
    @0
    csp
    @11
    cA
    cF
    fveq2
    oveq2d
    eqeq12d
    ralbidv
    @11
    chil
    wcel
    #
    @13
    @0
    cG
    cfv
    #
    @0
    vw
    cv
    #
    csp
    co
    #
    wceq
    #
    vf
    chil
    wral
    #
    vw
    chil
    crab
    #
    wcel
    #
    @16
    @19
    @13
    cB
    @25
    @19
    cB
    cvv
    wcel
    @13
    cB
    wceq
    cB
    vv
    cv
    #
    cT
    cfv
    #
    @11
    csp
    co
    #
    @27
    @21
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    #
    vw
    chil
    crio
    #
    cvv
    cnlnadjlem.4
    @32
    vw
    chil
    riotaex
    eqeltri
    vy
    chil
    cB
    cvv
    cF
    cnlnadjlem.5
    fvmpt2
    mpan2
    @19
    cB
    @24
    vw
    chil
    crio
    #
    @25
    cB
    @33
    @34
    cnlnadjlem.4
    @32
    @24
    vw
    chil
    @21
    chil
    wcel
    #
    @32
    @12
    @22
    wceq
    #
    vf
    chil
    wral
    #
    @24
    @32
    @37
    wb
    @35
    @31
    @36
    vv
    vf
    chil
    @27
    @0
    wceq
    #
    @29
    @12
    @30
    @22
    @38
    @28
    @1
    @11
    csp
    @27
    @0
    cT
    fveq2
    oveq1d
    @27
    @0
    @21
    csp
    oveq1
    eqeq12d
    cbvralv
    a1i
    @23
    @36
    vf
    chil
    @0
    chil
    wcel
    @20
    @12
    @22
    vy
    @0
    cT
    vg
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem1
    eqeq1d
    ralbiia
    #
    syl6bbr
    riotabiia
    eqtri
    @19
    cG
    clf
    ccnfn
    cin
    wcel
    #
    @24
    vw
    chil
    wreu
    @34
    @25
    wcel
    @19
    cG
    clf
    wcel
    cG
    ccnfn
    wcel
    wa
    @40
    vy
    cT
    vg
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem2
    cG
    clf
    ccnfn
    elin
    sylibr
    vw
    vf
    cG
    riesz4
    @24
    vw
    chil
    riotacl2
    3syl
    syl5eqel
    eqeltrd
    @26
    @13
    chil
    wcel
    @16
    @24
    @16
    vw
    @13
    chil
    @24
    @37
    @21
    @13
    wceq
    #
    @16
    @39
    @41
    @36
    @15
    vf
    chil
    @41
    @22
    @14
    @12
    @21
    @13
    @0
    csp
    oveq2
    eqeq2d
    ralbidv
    syl5bb
    elrab
    simprbi
    syl
    vtoclgaf
    @5
    @10
    vf
    cC
    chil
    @0
    cC
    wceq
    #
    @2
    @8
    @4
    @9
    @42
    @1
    @7
    cA
    csp
    @0
    cC
    cT
    fveq2
    oveq1d
    @0
    cC
    @3
    csp
    oveq1
    eqeq12d
    rspccva
    sylan
end
