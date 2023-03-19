include "wfun.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "wa.mm"
include "wfn.mm"
include "wss.mm"
include "cdm.mm"
include "wceq.mm"
include "simpr.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "wrex.mm"
include "wb.mm"
include "fliftel.mm"
include "exbidv.mm"
include "adantr.mm"
include "rexcom4.mm"
include "wcel.mm"
include "elisset.mm"
include "syl.mm"
include "biantrud.mm"
include "19.42v.mm"
include "syl6rbbr.mm"
include "rexbidva.mm"
include "syl5bbr.mm"
include "bitrd.mm"
include "abbidv.mm"
include "df-dm.mm"
include "eqid.mm"
include "rnmpt.mm"
include "3eqtr4g.mm"
include "df-fn.mm"
include "sylanbrc.mm"
include "cxp.mm"
include "fliftrel.mm"
include "rnss.mm"
include "rnxpss.mm"
include "syl6ss.mm"
include "df-f.mm"
include "ex.mm"
include "ffun.mm"
include "impbid1.mm"

theorem fliftf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cY: class Y
  let cD: class D
  assume flift.1: |- F = ran ( x e. X |-> <. A , B >. )
  assume flift.2: |- ( ( ph /\ x e. X ) -> A e. R )
  assume flift.3: |- ( ( ph /\ x e. X ) -> B e. S )

  disjoint R x
  disjoint ph x
  disjoint X x
  disjoint S x
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint B z
  disjoint u x
  disjoint C u
  disjoint v x
  disjoint C v
  disjoint x z
  disjoint C x
  disjoint C z
  disjoint x y
  disjoint R y
  disjoint R z
  disjoint Y x
  disjoint D u
  disjoint D v
  disjoint D x
  disjoint D z
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint F z
  disjoint ph u
  disjoint ph v
  disjoint ph y
  disjoint ph z
  disjoint X u
  disjoint X v
  disjoint X y
  disjoint X z
  disjoint S y
  disjoint S z
  assert |- ( ph -> ( Fun F <-> F : ran ( x e. X |-> A ) --> S ) )

  proof
    wph
    cF
    wfun
    #
    vx
    cX
    cA
    cmpt
    #
    crn
    #
    cS
    cF
    wf
    #
    wph
    @0
    @3
    wph
    @0
    wa
    #
    cF
    @2
    wfn
    #
    cF
    crn
    #
    cS
    wss
    @3
    @4
    @0
    cF
    cdm
    #
    @2
    wceq
    @5
    wph
    @0
    simpr
    @4
    vy
    cv
    #
    vz
    cv
    #
    cF
    wbr
    #
    vz
    wex
    #
    vy
    cab
    @8
    cA
    wceq
    #
    vx
    cX
    wrex
    #
    vy
    cab
    @7
    @2
    @4
    @11
    @13
    vy
    @4
    @11
    @12
    @9
    cB
    wceq
    #
    wa
    #
    vx
    cX
    wrex
    #
    vz
    wex
    #
    @13
    wph
    @11
    @17
    wb
    @0
    wph
    @10
    @16
    vz
    wph
    vx
    cA
    cB
    @8
    @9
    cR
    cS
    cF
    cX
    flift.1
    flift.2
    flift.3
    fliftel
    exbidv
    adantr
    @17
    @15
    vz
    wex
    #
    vx
    cX
    wrex
    #
    @4
    @13
    @15
    vx
    vz
    cX
    rexcom4
    wph
    @19
    @13
    wb
    @0
    wph
    @18
    @12
    vx
    cX
    wph
    vx
    cv
    cX
    wcel
    wa
    #
    @12
    @12
    @14
    vz
    wex
    #
    wa
    @18
    @20
    @21
    @12
    @20
    cB
    cS
    wcel
    @21
    flift.3
    vz
    cB
    cS
    elisset
    syl
    biantrud
    @12
    @14
    vz
    19.42v
    syl6rbbr
    rexbidva
    adantr
    syl5bbr
    bitrd
    abbidv
    vy
    vz
    cF
    df-dm
    vx
    vy
    cX
    cA
    @1
    @1
    eqid
    rnmpt
    3eqtr4g
    cF
    @2
    df-fn
    sylanbrc
    @4
    @6
    cR
    cS
    cxp
    #
    crn
    #
    cS
    @4
    cF
    @22
    wss
    #
    @6
    @23
    wss
    wph
    @24
    @0
    wph
    vx
    cA
    cB
    cR
    cS
    cF
    cX
    flift.1
    flift.2
    flift.3
    fliftrel
    adantr
    cF
    @22
    rnss
    syl
    cR
    cS
    rnxpss
    syl6ss
    @2
    cS
    cF
    df-f
    sylanbrc
    ex
    @2
    cS
    cF
    ffun
    impbid1
end
