include "chil.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wb.mm"
include "ccj.mm"
include "ffvelrn.mm"
include "ax-his1.mm"
include "sylan.mm"
include "adantrl.mm"
include "sylan2.mm"
include "adantll.mm"
include "eqeq12d.mm"
include "ancoms.mm"
include "cc.mm"
include "hicl.mm"
include "cj11.mm"
include "syl2anc.mm"
include "bitr2d.mm"
include "an4s.mm"
include "anassrs.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "ralbidva.mm"
include "ralcom.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "ralbidv.mm"
include "cbvralv.mm"
include "bitr4i.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "ralbii.mm"
include "3bitri.mm"
include "syl6rbbr.mm"

theorem adjsym
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let vz: setvar z
  let vu: setvar u
  let vv: setvar v

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint x z
  disjoint y z
  disjoint S z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint T u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint T v
  disjoint T z
  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H ) -> ( A. x e. ~H A. y e. ~H ( x .ih ( S ` y ) ) = ( ( T ` x ) .ih y ) <-> A. x e. ~H A. y e. ~H ( x .ih ( T ` y ) ) = ( ( S ` x ) .ih y ) ) )

  proof
    chil
    chil
    cS
    wf
    #
    chil
    chil
    cT
    wf
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    #
    csp
    co
    #
    @3
    cS
    cfv
    #
    @4
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    #
    vx
    chil
    wral
    @4
    @7
    csp
    co
    #
    @5
    @3
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    #
    vx
    chil
    wral
    #
    @3
    @4
    cS
    cfv
    #
    csp
    co
    #
    @3
    cT
    cfv
    #
    @4
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    @2
    @10
    @14
    vx
    chil
    @2
    @3
    chil
    wcel
    #
    wa
    #
    @9
    @13
    vy
    chil
    @23
    @4
    chil
    wcel
    #
    wa
    @9
    @12
    @11
    wceq
    #
    @13
    @2
    @22
    @24
    @9
    @25
    wb
    #
    @0
    @22
    @1
    @24
    @26
    @0
    @22
    wa
    #
    @1
    @24
    wa
    #
    wa
    #
    @25
    @6
    ccj
    cfv
    #
    @8
    ccj
    cfv
    #
    wceq
    #
    @9
    @28
    @27
    @25
    @32
    wb
    @28
    @27
    wa
    @12
    @30
    @11
    @31
    @28
    @22
    @12
    @30
    wceq
    #
    @0
    @28
    @5
    chil
    wcel
    #
    @22
    @33
    chil
    chil
    @4
    cT
    ffvelrn
    #
    @5
    @3
    ax-his1
    sylan
    adantrl
    @24
    @27
    @11
    @31
    wceq
    #
    @1
    @27
    @24
    @7
    chil
    wcel
    #
    @36
    chil
    chil
    @3
    cS
    ffvelrn
    #
    @4
    @7
    ax-his1
    sylan2
    adantll
    eqeq12d
    ancoms
    @29
    @6
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    @32
    @9
    wb
    @22
    @28
    @39
    @0
    @28
    @22
    @34
    @39
    @35
    @3
    @5
    hicl
    sylan2
    adantll
    @27
    @24
    @40
    @1
    @27
    @37
    @24
    @40
    @38
    @7
    @4
    hicl
    sylan
    adantrl
    @6
    @8
    cj11
    syl2anc
    bitr2d
    an4s
    anassrs
    @12
    @11
    eqcom
    syl6bb
    ralbidva
    ralbidva
    @21
    @3
    vz
    cv
    #
    cS
    cfv
    #
    csp
    co
    #
    @18
    @41
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    #
    vz
    chil
    wral
    #
    @4
    @42
    csp
    co
    #
    @5
    @41
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    #
    vz
    chil
    wral
    @15
    @21
    @20
    vx
    chil
    wral
    #
    vy
    chil
    wral
    @47
    @20
    vx
    vy
    chil
    chil
    ralcom
    @46
    @52
    vz
    vy
    chil
    vz
    vy
    weq
    #
    @45
    @20
    vx
    chil
    @53
    @43
    @17
    @44
    @19
    @53
    @42
    @16
    @3
    csp
    @41
    @4
    cS
    fveq2
    oveq2d
    @41
    @4
    @18
    csp
    oveq2
    eqeq12d
    ralbidv
    cbvralv
    bitr4i
    @46
    @51
    vz
    chil
    @45
    @50
    vx
    vy
    chil
    vx
    vy
    weq
    #
    @43
    @48
    @44
    @49
    @3
    @4
    @42
    csp
    oveq1
    @54
    @18
    @5
    @41
    csp
    @3
    @4
    cT
    fveq2
    oveq1d
    eqeq12d
    cbvralv
    ralbii
    @51
    @14
    vz
    vx
    chil
    vz
    vx
    weq
    #
    @50
    @13
    vy
    chil
    @55
    @48
    @11
    @49
    @12
    @55
    @42
    @7
    @4
    csp
    @41
    @3
    cS
    fveq2
    oveq2d
    @41
    @3
    @5
    csp
    oveq2
    eqeq12d
    ralbidv
    cbvralv
    3bitri
    syl6rbbr
end
