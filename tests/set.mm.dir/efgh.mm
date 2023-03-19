include "cc.mm"
include "wcel.mm"
include "ccnfld.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "ce.mm"
include "simp1l.mm"
include "wss.mm"
include "simp1r.mm"
include "cnfldbas.mm"
include "subgss.mm"
include "syl.mm"
include "simp2.mm"
include "sseldd.mm"
include "simp3.mm"
include "adddid.mm"
include "fveq2d.mm"
include "wceq.mm"
include "mulcld.mm"
include "efadd.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "cv.mm"
include "cvv.mm"
include "cmpt.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "a1i.mm"
include "adantl.mm"
include "cnfldadd.mm"
include "subgcl.mm"
include "3adant1l.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem efgh
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cX: class X
  let vy: setvar y
  assume efgh.1: |- F = ( x e. X |-> ( exp ` ( A x. x ) ) )

  disjoint A x
  disjoint X x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint X y
  assert |- ( ( ( A e. CC /\ X e. ( SubGrp ` CCfld ) ) /\ B e. X /\ C e. X ) -> ( F ` ( B + C ) ) = ( ( F ` B ) x. ( F ` C ) ) )

  proof
    cA
    cc
    wcel
    #
    cX
    ccnfld
    csubg
    cfv
    wcel
    #
    wa
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    caddc
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cA
    cB
    cmul
    co
    #
    ce
    cfv
    #
    cA
    cC
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    @6
    cF
    cfv
    cB
    cF
    cfv
    #
    cC
    cF
    cfv
    #
    cmul
    co
    @5
    @8
    @9
    @11
    caddc
    co
    #
    ce
    cfv
    #
    @13
    @5
    @7
    @16
    ce
    @5
    cA
    cB
    cC
    @0
    @1
    @3
    @4
    simp1l
    #
    @5
    cX
    cc
    cB
    @5
    @1
    cX
    cc
    wss
    @0
    @1
    @3
    @4
    simp1r
    cc
    cX
    ccnfld
    cnfldbas
    subgss
    syl
    #
    @2
    @3
    @4
    simp2
    #
    sseldd
    #
    @5
    cX
    cc
    cC
    @19
    @2
    @3
    @4
    simp3
    #
    sseldd
    #
    adddid
    fveq2d
    @5
    @9
    cc
    wcel
    @11
    cc
    wcel
    @17
    @13
    wceq
    @5
    cA
    cB
    @18
    @21
    mulcld
    @5
    cA
    cC
    @18
    @23
    mulcld
    @9
    @11
    efadd
    syl2anc
    eqtrd
    @5
    vy
    @6
    cA
    vy
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    @8
    cX
    cF
    cvv
    cF
    vy
    cX
    @26
    cmpt
    #
    wceq
    @5
    cF
    vx
    cX
    cA
    vx
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmpt
    @27
    efgh.1
    vx
    vy
    cX
    @30
    @26
    @28
    @24
    wceq
    @29
    @25
    ce
    @28
    @24
    cA
    cmul
    oveq2
    fveq2d
    cbvmptv
    eqtri
    a1i
    #
    @24
    @6
    wceq
    #
    @26
    @8
    wceq
    @5
    @32
    @25
    @7
    ce
    @24
    @6
    cA
    cmul
    oveq2
    fveq2d
    adantl
    @1
    @3
    @4
    @6
    cX
    wcel
    @0
    caddc
    cX
    ccnfld
    cB
    cC
    cnfldadd
    subgcl
    3adant1l
    @5
    @7
    ce
    fvexd
    fvmptd
    @5
    @14
    @10
    @15
    @12
    cmul
    @5
    vy
    cB
    @26
    @10
    cX
    cF
    cvv
    @31
    @24
    cB
    wceq
    #
    @26
    @10
    wceq
    @5
    @33
    @25
    @9
    ce
    @24
    cB
    cA
    cmul
    oveq2
    fveq2d
    adantl
    @20
    @5
    @9
    ce
    fvexd
    fvmptd
    @5
    vy
    cC
    @26
    @12
    cX
    cF
    cvv
    @31
    @24
    cC
    wceq
    #
    @26
    @12
    wceq
    @5
    @34
    @25
    @11
    ce
    @24
    cC
    cA
    cmul
    oveq2
    fveq2d
    adantl
    @22
    @5
    @11
    ce
    fvexd
    fvmptd
    oveq12d
    3eqtr4d
end
