include "wcel.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cxp.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "wa.mm"
include "cvv.mm"
include "3simpa.mm"
include "xpexg.mm"
include "relexp1g.mm"
include "3syl.mm"
include "cn.mm"
include "ccom.mm"
include "simp2.mm"
include "simp1.mm"
include "relexpsucnnr.mm"
include "syl2anc.mm"
include "simp3.mm"
include "coeq1d.mm"
include "simp23.mm"
include "xpcoidgend.mm"
include "3eqtrd.mm"
include "3exp.mm"
include "a2d.mm"
include "nnind.mm"

theorem relexpxpnnidm
  let cA: class A
  let cB: class B
  let cU: class U
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( N e. NN -> ( ( A e. U /\ B e. V /\ ( A i^i B ) =/= (/) ) -> ( ( A X. B ) ^r N ) = ( A X. B ) ) )

  proof
    cA
    cU
    wcel
    #
    cB
    cV
    wcel
    #
    cA
    cB
    cin
    c0
    wne
    #
    w3a
    #
    cA
    cB
    cxp
    #
    vx
    cv
    #
    crelexp
    co
    #
    @4
    wceq
    #
    wi
    @3
    @4
    c1
    crelexp
    co
    #
    @4
    wceq
    #
    wi
    @3
    @4
    vy
    cv
    #
    crelexp
    co
    #
    @4
    wceq
    #
    wi
    @3
    @4
    @10
    c1
    caddc
    co
    #
    crelexp
    co
    #
    @4
    wceq
    #
    wi
    @3
    @4
    cN
    crelexp
    co
    #
    @4
    wceq
    #
    wi
    vx
    vy
    cN
    @5
    c1
    wceq
    #
    @7
    @9
    @3
    @18
    @6
    @8
    @4
    @5
    c1
    @4
    crelexp
    oveq2
    eqeq1d
    imbi2d
    vx
    vy
    weq
    #
    @7
    @12
    @3
    @19
    @6
    @11
    @4
    @5
    @10
    @4
    crelexp
    oveq2
    eqeq1d
    imbi2d
    @5
    @13
    wceq
    #
    @7
    @15
    @3
    @20
    @6
    @14
    @4
    @5
    @13
    @4
    crelexp
    oveq2
    eqeq1d
    imbi2d
    @5
    cN
    wceq
    #
    @7
    @17
    @3
    @21
    @6
    @16
    @4
    @5
    cN
    @4
    crelexp
    oveq2
    eqeq1d
    imbi2d
    @3
    @0
    @1
    wa
    #
    @4
    cvv
    wcel
    #
    @9
    @0
    @1
    @2
    3simpa
    #
    cA
    cB
    cU
    cV
    xpexg
    #
    @4
    cvv
    relexp1g
    3syl
    @10
    cn
    wcel
    #
    @3
    @12
    @15
    @26
    @3
    @12
    @15
    @26
    @3
    @12
    w3a
    #
    @14
    @11
    @4
    ccom
    #
    @4
    @4
    ccom
    @4
    @27
    @23
    @26
    @14
    @28
    wceq
    @27
    @3
    @22
    @23
    @26
    @3
    @12
    simp2
    @24
    @25
    3syl
    @26
    @3
    @12
    simp1
    @4
    @10
    cvv
    relexpsucnnr
    syl2anc
    @27
    @11
    @4
    @4
    @26
    @3
    @12
    simp3
    coeq1d
    @27
    cA
    cB
    @26
    @0
    @1
    @2
    @12
    simp23
    xpcoidgend
    3eqtrd
    3exp
    a2d
    nnind
end
