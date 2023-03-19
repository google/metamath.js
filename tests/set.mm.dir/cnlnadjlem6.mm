include "clo.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "cnlnadjlem3.mm"
include "fmpti.mm"
include "wa.mm"
include "csp.mm"
include "caddc.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "adantl.mm"
include "hvmulcl.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "his7.mm"
include "syl3anc.mm"
include "hvaddcl.mm"
include "sylan.mm"
include "cnlnadjlem5.mm"
include "ccj.mm"
include "cmul.mm"
include "simpll.mm"
include "his5.mm"
include "simpr.mm"
include "cnlnadjlem4.mm"
include "ad2antlr.mm"
include "adantll.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "adantlr.mm"
include "oveq12d.mm"
include "sylan2.mm"
include "3eqtr3d.mm"
include "ralrimiva.mm"
include "wb.mm"
include "syl.mm"
include "syl2an.mm"
include "hial2eq2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "rgen2.mm"
include "ellnop.mm"
include "mpbir2an.mm"

theorem cnlnadjlem6
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let cB: class B
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vx: setvar x
  let cC: class C
  assume cnlnadjlem.1: |- T e. LinOp
  assume cnlnadjlem.2: |- T e. ContOp
  assume cnlnadjlem.3: |- G = ( g e. ~H |-> ( ( T ` g ) .ih y ) )
  assume cnlnadjlem.4: |- B = ( iota_ w e. ~H A. v e. ~H ( ( T ` v ) .ih y ) = ( v .ih w ) )
  assume cnlnadjlem.5: |- F = ( y e. ~H |-> B )

  disjoint g v
  disjoint g w
  disjoint g y
  disjoint v w
  disjoint v y
  disjoint w y
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
  disjoint A g
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
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
  assert |- F e. LinOp

  proof
    cF
    clo
    wcel
    chil
    chil
    cF
    wf
    vx
    cv
    #
    vf
    cv
    #
    csm
    co
    #
    vz
    cv
    #
    cva
    co
    #
    cF
    cfv
    #
    @0
    @1
    cF
    cfv
    #
    csm
    co
    #
    @3
    cF
    cfv
    #
    cva
    co
    #
    wceq
    #
    vz
    chil
    wral
    #
    vf
    chil
    wral
    vx
    cc
    wral
    vy
    chil
    chil
    cB
    cF
    cnlnadjlem.5
    vy
    vw
    vv
    cB
    cT
    vg
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem3
    fmpti
    @11
    vx
    vf
    cc
    chil
    @0
    cc
    wcel
    #
    @1
    chil
    wcel
    #
    wa
    #
    @10
    vz
    chil
    @14
    @3
    chil
    wcel
    #
    wa
    #
    vt
    cv
    #
    @5
    csp
    co
    #
    @17
    @9
    csp
    co
    #
    wceq
    #
    vt
    chil
    wral
    #
    @10
    @16
    @20
    vt
    chil
    @16
    @17
    chil
    wcel
    #
    wa
    #
    @17
    cT
    cfv
    #
    @4
    csp
    co
    #
    @24
    @2
    csp
    co
    #
    @24
    @3
    csp
    co
    #
    caddc
    co
    #
    @18
    @19
    @23
    @24
    chil
    wcel
    #
    @2
    chil
    wcel
    #
    @15
    @25
    @28
    wceq
    @22
    @29
    @16
    chil
    chil
    @17
    cT
    cT
    cnlnadjlem.1
    lnopfi
    ffvelrni
    #
    adantl
    @14
    @30
    @15
    @22
    @0
    @1
    hvmulcl
    #
    ad2antrr
    @14
    @15
    @22
    simplr
    @24
    @2
    @3
    his7
    syl3anc
    @16
    @4
    chil
    wcel
    #
    @22
    @25
    @18
    wceq
    @14
    @30
    @15
    @33
    @32
    @2
    @3
    hvaddcl
    sylan
    #
    vy
    vw
    vv
    @4
    cB
    @17
    cT
    vg
    cF
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem.5
    cnlnadjlem5
    sylan
    @23
    @28
    @17
    @7
    csp
    co
    #
    @17
    @8
    csp
    co
    #
    caddc
    co
    #
    @19
    @23
    @26
    @35
    @27
    @36
    caddc
    @14
    @22
    @26
    @35
    wceq
    @15
    @14
    @22
    wa
    #
    @26
    @0
    ccj
    cfv
    #
    @24
    @1
    csp
    co
    #
    cmul
    co
    #
    @35
    @38
    @12
    @29
    @13
    @26
    @41
    wceq
    @12
    @13
    @22
    simpll
    #
    @22
    @29
    @14
    @31
    adantl
    @12
    @13
    @22
    simplr
    @0
    @24
    @1
    his5
    syl3anc
    @38
    @35
    @39
    @17
    @6
    csp
    co
    #
    cmul
    co
    #
    @41
    @38
    @12
    @22
    @6
    chil
    wcel
    #
    @35
    @44
    wceq
    @42
    @14
    @22
    simpr
    @13
    @45
    @12
    @22
    vy
    vw
    vv
    @1
    cB
    cT
    vg
    cF
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem.5
    cnlnadjlem4
    #
    ad2antlr
    @0
    @17
    @6
    his5
    syl3anc
    @38
    @40
    @43
    @39
    cmul
    @13
    @22
    @40
    @43
    wceq
    @12
    vy
    vw
    vv
    @1
    cB
    @17
    cT
    vg
    cF
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem.5
    cnlnadjlem5
    adantll
    oveq2d
    eqtr4d
    eqtr4d
    adantlr
    @15
    @22
    @27
    @36
    wceq
    @14
    vy
    vw
    vv
    @3
    cB
    @17
    cT
    vg
    cF
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem.5
    cnlnadjlem5
    adantll
    oveq12d
    @23
    @22
    @7
    chil
    wcel
    #
    @8
    chil
    wcel
    #
    @19
    @37
    wceq
    @16
    @22
    simpr
    @14
    @47
    @15
    @22
    @13
    @12
    @45
    @47
    @46
    @0
    @6
    hvmulcl
    sylan2
    #
    ad2antrr
    @15
    @48
    @14
    @22
    vy
    vw
    vv
    @3
    cB
    cT
    vg
    cF
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem.5
    cnlnadjlem4
    #
    ad2antlr
    @17
    @7
    @8
    his7
    syl3anc
    eqtr4d
    3eqtr3d
    ralrimiva
    @16
    @5
    chil
    wcel
    #
    @9
    chil
    wcel
    #
    @21
    @10
    wb
    @16
    @33
    @51
    @34
    vy
    vw
    vv
    @4
    cB
    cT
    vg
    cF
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem.5
    cnlnadjlem4
    syl
    @14
    @47
    @48
    @52
    @15
    @49
    @50
    @7
    @8
    hvaddcl
    syl2an
    vt
    @5
    @9
    hial2eq2
    syl2anc
    mpbid
    ralrimiva
    rgen2
    vx
    vf
    vz
    cF
    ellnop
    mpbir2an
end
