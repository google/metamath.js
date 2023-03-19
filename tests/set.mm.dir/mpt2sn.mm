include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "csb.mm"
include "cmpt.mm"
include "cop.mm"
include "wceq.mm"
include "xpsng.mm"
include "3adant3.mm"
include "mpteq1d.mm"
include "cmpt2.mm"
include "mpt2mpts.mm"
include "eqtri.mm"
include "a1i.mm"
include "cvv.mm"
include "wa.mm"
include "wi.mm"
include "op2ndg.mm"
include "fveq2.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "op1stg.mm"
include "simp1.mm"
include "simpl2.mm"
include "adantl.mm"
include "sylan9eq.mm"
include "csbied.mm"
include "adantr.mm"
include "wb.mm"
include "csbeq1.mm"
include "csbeq2dv.mm"
include "bitrd.mm"
include "syl5ibrcom.mm"
include "mp2and.mm"
include "opex.mm"
include "simp3.mm"
include "fmptsnd.mm"
include "3eqtr4d.mm"

theorem mpt2sn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W
  let vp: setvar p
  assume mpt2sn.f: |- F = ( x e. { A } , y e. { B } |-> C )
  assume mpt2sn.a: |- ( x = A -> C = D )
  assume mpt2sn.b: |- ( y = B -> D = E )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint E x
  disjoint E y
  disjoint U x
  disjoint U y
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  disjoint A p
  disjoint p x
  disjoint p y
  disjoint B p
  disjoint C p
  disjoint E p
  disjoint U p
  disjoint V p
  disjoint W p
  assert |- ( ( A e. V /\ B e. W /\ E e. U ) -> F = { <. <. A , B >. , E >. } )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cE
    cU
    wcel
    #
    w3a
    #
    vp
    cA
    csn
    #
    cB
    csn
    #
    cxp
    #
    vx
    vp
    cv
    #
    c1st
    cfv
    #
    vy
    @7
    c2nd
    cfv
    #
    cC
    csb
    #
    csb
    #
    cmpt
    #
    vp
    cA
    cB
    cop
    #
    csn
    #
    @11
    cmpt
    cF
    @13
    cE
    cop
    csn
    @3
    vp
    @6
    @14
    @11
    @0
    @1
    @6
    @14
    wceq
    @2
    cA
    cB
    cV
    cW
    xpsng
    3adant3
    mpteq1d
    cF
    @12
    wceq
    @3
    cF
    vx
    vy
    @4
    @5
    cC
    cmpt2
    @12
    mpt2sn.f
    vx
    vy
    vp
    @4
    @5
    cC
    mpt2mpts
    eqtri
    a1i
    @3
    vp
    @13
    @11
    cE
    cvv
    cU
    @3
    @7
    @13
    wceq
    #
    wa
    #
    @9
    cB
    wceq
    #
    @8
    cA
    wceq
    #
    @11
    cE
    wceq
    #
    @3
    @15
    @17
    @0
    @1
    @15
    @17
    wi
    @2
    @0
    @1
    wa
    #
    @13
    c2nd
    cfv
    #
    cB
    wceq
    @15
    @17
    cA
    cB
    cV
    cW
    op2ndg
    @15
    @21
    @9
    cB
    @15
    @9
    @21
    @7
    @13
    c2nd
    fveq2
    eqcomd
    eqeq1d
    syl5ibcom
    3adant3
    imp
    @3
    @15
    @18
    @0
    @1
    @15
    @18
    wi
    @2
    @20
    @13
    c1st
    cfv
    #
    cA
    wceq
    @15
    @18
    cA
    cB
    cV
    cW
    op1stg
    @15
    @22
    @8
    cA
    @15
    @8
    @22
    @7
    @13
    c1st
    fveq2
    eqcomd
    eqeq1d
    syl5ibcom
    3adant3
    imp
    @16
    @19
    @17
    @18
    wa
    #
    vx
    cA
    vy
    cB
    cC
    csb
    #
    csb
    #
    cE
    wceq
    #
    @3
    @26
    @15
    @3
    vx
    cA
    @24
    cE
    cV
    @0
    @1
    @2
    simp1
    @3
    vx
    cv
    cA
    wceq
    #
    wa
    #
    vy
    cB
    cC
    cE
    cW
    @0
    @1
    @2
    @27
    simpl2
    @28
    vy
    cv
    cB
    wceq
    cC
    cD
    cE
    @27
    cC
    cD
    wceq
    @3
    mpt2sn.a
    adantl
    mpt2sn.b
    sylan9eq
    csbied
    csbied
    adantr
    @23
    @19
    vx
    cA
    @10
    csb
    #
    cE
    wceq
    #
    @26
    @18
    @19
    @30
    wb
    @17
    @18
    @11
    @29
    cE
    vx
    @8
    cA
    @10
    csbeq1
    eqeq1d
    adantl
    @23
    @29
    @25
    cE
    @23
    vx
    cA
    @10
    @24
    @17
    @10
    @24
    wceq
    @18
    vy
    @9
    cB
    cC
    csbeq1
    adantr
    csbeq2dv
    eqeq1d
    bitrd
    syl5ibrcom
    mp2and
    @13
    cvv
    wcel
    @3
    cA
    cB
    opex
    a1i
    @0
    @1
    @2
    simp3
    fmptsnd
    3eqtr4d
end
