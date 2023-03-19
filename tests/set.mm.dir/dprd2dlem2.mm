include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c2nd.mm"
include "c1st.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cdprd.mm"
include "cop.mm"
include "df-ov.mm"
include "wceq.mm"
include "wbr.mm"
include "wrel.mm"
include "1st2nd.mm"
include "sylan.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "df-br.mm"
include "sylibr.mm"
include "wb.mm"
include "adantr.mm"
include "elrelimasn.mm"
include "syl.mm"
include "mpbird.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "cdm.mm"
include "wral.mm"
include "wss.mm"
include "1stdm.mm"
include "sseldd.mm"
include "ralrimiva.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "oveq1.mm"
include "mpteq12dv.mm"
include "breq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "dmmpti.mm"
include "a1i.mm"
include "dprdub.mm"
include "eqsstr3d.mm"

theorem dprd2dlem2
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let cI: class I
  let cK: class K
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume dprd2d.1: |- ( ph -> Rel A )
  assume dprd2d.2: |- ( ph -> S : A --> ( SubGrp ` G ) )
  assume dprd2d.3: |- ( ph -> dom A C_ I )
  assume dprd2d.4: |- ( ( ph /\ i e. I ) -> G dom DProd ( j e. ( A " { i } ) |-> ( i S j ) ) )
  assume dprd2d.5: |- ( ph -> G dom DProd ( i e. I |-> ( G DProd ( j e. ( A " { i } ) |-> ( i S j ) ) ) ) )
  assume dprd2d.k: |- K = ( mrCls ` ( SubGrp ` G ) )

  disjoint i j
  disjoint A i
  disjoint A j
  disjoint G i
  disjoint G j
  disjoint I i
  disjoint K i
  disjoint i ph
  disjoint j ph
  disjoint S i
  disjoint S j
  disjoint X i
  disjoint X j
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint C i
  disjoint C k
  disjoint C x
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint K k
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint S k
  disjoint S x
  disjoint S y
  assert |- ( ( ph /\ X e. A ) -> ( S ` X ) C_ ( G DProd ( j e. ( A " { ( 1st ` X ) } ) |-> ( ( 1st ` X ) S j ) ) ) )

  proof
    wph
    cX
    cA
    wcel
    #
    wa
    #
    cX
    cS
    cfv
    #
    cX
    c2nd
    cfv
    #
    vj
    cA
    cX
    c1st
    cfv
    #
    csn
    #
    cima
    #
    @4
    vj
    cv
    #
    cS
    co
    #
    cmpt
    #
    cfv
    #
    cG
    @9
    cdprd
    co
    @1
    @4
    @3
    cS
    co
    #
    @4
    @3
    cop
    #
    cS
    cfv
    @10
    @2
    @4
    @3
    cS
    df-ov
    @1
    @3
    @6
    wcel
    #
    @10
    @11
    wceq
    @1
    @13
    @4
    @3
    cA
    wbr
    #
    @1
    @12
    cA
    wcel
    @14
    @1
    cX
    @12
    cA
    wph
    cA
    wrel
    #
    @0
    cX
    @12
    wceq
    dprd2d.1
    cX
    cA
    1st2nd
    sylan
    #
    wph
    @0
    simpr
    eqeltrrd
    @4
    @3
    cA
    df-br
    sylibr
    @1
    @15
    @13
    @14
    wb
    wph
    @15
    @0
    dprd2d.1
    adantr
    @4
    @3
    cA
    elrelimasn
    syl
    mpbird
    #
    vj
    @3
    @8
    @11
    @6
    @9
    @7
    @3
    @4
    cS
    oveq2
    @9
    eqid
    #
    @4
    @7
    cS
    ovex
    #
    fvmpt3i
    syl
    @1
    cX
    @12
    cS
    @16
    fveq2d
    3eqtr4a
    @1
    @9
    cG
    @6
    @3
    @1
    @4
    cI
    wcel
    cG
    vj
    cA
    vi
    cv
    #
    csn
    #
    cima
    #
    @20
    @7
    cS
    co
    #
    cmpt
    #
    cdprd
    cdm
    #
    wbr
    #
    vi
    cI
    wral
    #
    cG
    @9
    @25
    wbr
    #
    @1
    cA
    cdm
    #
    cI
    @4
    wph
    @29
    cI
    wss
    @0
    dprd2d.3
    adantr
    wph
    @15
    @0
    @4
    @29
    wcel
    dprd2d.1
    cX
    cA
    1stdm
    sylan
    sseldd
    wph
    @27
    @0
    wph
    @26
    vi
    cI
    dprd2d.4
    ralrimiva
    adantr
    @26
    @28
    vi
    @4
    cI
    @20
    @4
    wceq
    #
    @24
    @9
    cG
    @25
    @30
    vj
    @22
    @23
    @6
    @8
    @30
    @21
    @5
    cA
    @20
    @4
    sneq
    imaeq2d
    @20
    @4
    @7
    cS
    oveq1
    mpteq12dv
    breq2d
    rspcv
    sylc
    @9
    cdm
    @6
    wceq
    @1
    vj
    @6
    @8
    @9
    @19
    @18
    dmmpti
    a1i
    @17
    dprdub
    eqsstr3d
end
