include "ccom.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "csb.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wf.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfcsb.mm"
include "weq.mm"
include "csbeq1a.mm"
include "sylan9eq.mm"
include "cbvmpt2.mm"
include "cop.mm"
include "wceq.mm"
include "vex.mm"
include "op2ndd.mm"
include "csbeq1d.mm"
include "op1std.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "mpt2mpt.mm"
include "eqtr4i.mm"
include "fmpt.mm"
include "sylibr.mm"
include "syl6eq.mm"
include "fmptcos.mm"
include "wa.mm"
include "w3a.mm"
include "3impb.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "syl.mm"
include "mpt2eq3dva.mm"
include "syl5eq.mm"

theorem fmpt2co
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume fmpt2co.1: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> R e. C )
  assume fmpt2co.2: |- ( ph -> F = ( x e. A , y e. B |-> R ) )
  assume fmpt2co.3: |- ( ph -> G = ( z e. C |-> S ) )
  assume fmpt2co.4: |- ( z = R -> S = T )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint A x
  disjoint A y
  disjoint R z
  disjoint T z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint u z
  disjoint C u
  disjoint w z
  disjoint C w
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint R u
  disjoint v z
  disjoint R v
  disjoint R w
  assert |- ( ph -> ( G o. F ) = ( x e. A , y e. B |-> T ) )

  proof
    wph
    cG
    cF
    ccom
    vw
    cA
    cB
    cxp
    #
    vz
    vy
    vw
    cv
    #
    c2nd
    cfv
    #
    vx
    @1
    c1st
    cfv
    #
    cR
    csb
    #
    csb
    #
    cS
    csb
    #
    cmpt
    #
    vx
    vy
    cA
    cB
    cT
    cmpt2
    #
    wph
    vw
    vz
    @0
    cC
    @5
    cS
    cF
    cG
    wph
    @0
    cC
    vx
    vy
    cA
    cB
    cR
    cmpt2
    #
    wf
    #
    @5
    cC
    wcel
    vw
    @0
    wral
    wph
    cR
    cC
    wcel
    #
    vy
    cB
    wral
    vx
    cA
    wral
    @10
    wph
    @11
    vx
    vy
    cA
    cB
    fmpt2co.1
    ralrimivva
    vx
    vy
    cA
    cB
    cR
    cC
    @9
    @9
    eqid
    fmpt2
    sylib
    vw
    @0
    cC
    @5
    @9
    @9
    vu
    vv
    cA
    cB
    vy
    vv
    cv
    #
    vx
    vu
    cv
    #
    cR
    csb
    #
    csb
    #
    cmpt2
    vw
    @0
    @5
    cmpt
    #
    vx
    vy
    vu
    vv
    cA
    cB
    cR
    @15
    vu
    cR
    nfcv
    vv
    cR
    nfcv
    vx
    vy
    @12
    @14
    vx
    @12
    nfcv
    vx
    @13
    cR
    nfcsb1v
    nfcsb
    #
    vy
    @12
    @14
    nfcsb1v
    #
    vx
    vu
    weq
    #
    vy
    vv
    weq
    #
    cR
    @14
    @15
    vx
    @13
    cR
    csbeq1a
    vy
    @12
    @14
    csbeq1a
    sylan9eq
    #
    cbvmpt2
    vu
    vv
    vw
    cA
    cB
    @5
    @15
    @1
    @13
    @12
    cop
    wceq
    #
    @5
    vy
    @12
    @4
    csb
    @15
    @22
    vy
    @2
    @12
    @4
    @13
    @12
    @1
    vu
    vex
    #
    vv
    vex
    #
    op2ndd
    csbeq1d
    @22
    vy
    @12
    @4
    @14
    @22
    vx
    @3
    @13
    cR
    @13
    @12
    @1
    @23
    @24
    op1std
    csbeq1d
    csbeq2dv
    eqtrd
    #
    mpt2mpt
    eqtr4i
    #
    fmpt
    sylibr
    wph
    cF
    @9
    @16
    fmpt2co.2
    @26
    syl6eq
    fmpt2co.3
    fmptcos
    wph
    @7
    vx
    vy
    cA
    cB
    vz
    cR
    cS
    csb
    #
    cmpt2
    #
    @8
    @7
    vu
    vv
    cA
    cB
    vz
    @15
    cS
    csb
    #
    cmpt2
    @28
    vu
    vv
    vw
    cA
    cB
    @6
    @29
    @22
    vz
    @5
    @15
    cS
    @25
    csbeq1d
    mpt2mpt
    vx
    vy
    vu
    vv
    cA
    cB
    @27
    @29
    vu
    @27
    nfcv
    vv
    @27
    nfcv
    vx
    vz
    @15
    cS
    @17
    vx
    cS
    nfcv
    nfcsb
    vy
    vz
    @15
    cS
    @18
    vy
    cS
    nfcv
    nfcsb
    @19
    @20
    wa
    vz
    cR
    @15
    cS
    @21
    csbeq1d
    cbvmpt2
    eqtr4i
    wph
    vx
    vy
    cA
    cB
    @27
    cT
    wph
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    w3a
    @11
    @27
    cT
    wceq
    wph
    @30
    @31
    @11
    fmpt2co.1
    3impb
    vz
    cR
    cS
    cT
    cC
    @11
    vz
    cT
    nfcvd
    fmpt2co.4
    csbiegf
    syl
    mpt2eq3dva
    syl5eq
    eqtrd
end
