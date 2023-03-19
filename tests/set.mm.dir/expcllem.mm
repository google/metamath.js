include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cexp.mm"
include "co.mm"
include "elnn0.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "cc.mm"
include "sseli.mm"
include "exp1.mm"
include "syl.mm"
include "ibir.mm"
include "wa.mm"
include "cmul.mm"
include "caovcl.mm"
include "ancoms.mm"
include "adantlr.mm"
include "wb.mm"
include "nnnn0.mm"
include "expp1.mm"
include "syl2an.mm"
include "adantr.mm"
include "mpbird.mm"
include "exp31.mm"
include "com12.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"
include "exp0.mm"
include "sylan9eqr.mm"
include "syl6eqel.mm"
include "jaodan.mm"
include "sylan2b.mm"

theorem expcllem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z
  let vw: setvar w
  assume expcllem.1: |- F C_ CC
  assume expcllem.2: |- ( ( x e. F /\ y e. F ) -> ( x x. y ) e. F )
  assume expcllem.3: |- 1 e. F

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint F z
  disjoint F w
  assert |- ( ( A e. F /\ B e. NN0 ) -> ( A ^ B ) e. F )

  proof
    cB
    cn0
    wcel
    cA
    cF
    wcel
    #
    cB
    cn
    wcel
    #
    cB
    cc0
    wceq
    #
    wo
    cA
    cB
    cexp
    co
    #
    cF
    wcel
    #
    cB
    elnn0
    @0
    @1
    @4
    @2
    @1
    @0
    @4
    @0
    cA
    vz
    cv
    #
    cexp
    co
    #
    cF
    wcel
    #
    wi
    @0
    cA
    c1
    cexp
    co
    #
    cF
    wcel
    #
    wi
    @0
    cA
    vw
    cv
    #
    cexp
    co
    #
    cF
    wcel
    #
    wi
    @0
    cA
    @10
    c1
    caddc
    co
    #
    cexp
    co
    #
    cF
    wcel
    #
    wi
    @0
    @4
    wi
    vz
    vw
    cB
    @5
    c1
    wceq
    #
    @7
    @9
    @0
    @16
    @6
    @8
    cF
    @5
    c1
    cA
    cexp
    oveq2
    eleq1d
    imbi2d
    @5
    @10
    wceq
    #
    @7
    @12
    @0
    @17
    @6
    @11
    cF
    @5
    @10
    cA
    cexp
    oveq2
    eleq1d
    imbi2d
    @5
    @13
    wceq
    #
    @7
    @15
    @0
    @18
    @6
    @14
    cF
    @5
    @13
    cA
    cexp
    oveq2
    eleq1d
    imbi2d
    @5
    cB
    wceq
    #
    @7
    @4
    @0
    @19
    @6
    @3
    cF
    @5
    cB
    cA
    cexp
    oveq2
    eleq1d
    imbi2d
    @0
    @9
    @0
    @8
    cA
    cF
    @0
    cA
    cc
    wcel
    #
    @8
    cA
    wceq
    cF
    cc
    cA
    expcllem.1
    sseli
    #
    cA
    exp1
    syl
    eleq1d
    ibir
    @10
    cn
    wcel
    #
    @0
    @12
    @15
    @0
    @22
    @12
    @15
    wi
    @0
    @22
    @12
    @15
    @0
    @22
    wa
    #
    @12
    wa
    @15
    @11
    cA
    cmul
    co
    #
    cF
    wcel
    #
    @0
    @12
    @25
    @22
    @12
    @0
    @25
    vx
    vy
    @11
    cA
    cF
    cmul
    expcllem.2
    caovcl
    ancoms
    adantlr
    @23
    @15
    @25
    wb
    @12
    @23
    @14
    @24
    cF
    @0
    @20
    @10
    cn0
    wcel
    @14
    @24
    wceq
    @22
    @21
    @10
    nnnn0
    cA
    @10
    expp1
    syl2an
    eleq1d
    adantr
    mpbird
    exp31
    com12
    a2d
    nnind
    impcom
    @0
    @2
    wa
    @3
    c1
    cF
    @2
    @0
    @3
    cA
    cc0
    cexp
    co
    #
    c1
    cB
    cc0
    cA
    cexp
    oveq2
    @0
    @20
    @26
    c1
    wceq
    @21
    cA
    exp0
    syl
    sylan9eqr
    expcllem.3
    syl6eqel
    jaodan
    sylan2b
end
