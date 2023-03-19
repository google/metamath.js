include "wcel.mm"
include "csb.mm"
include "co.mm"
include "wceq.mm"
include "cvv.mm"
include "wa.mm"
include "elex.mm"
include "cv.mm"
include "wi.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "cmpt2.mm"
include "nfmpt21.mm"
include "nfcxfr.mm"
include "nfov.mm"
include "nfeq.mm"
include "nfim.mm"
include "nfmpt22.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "ovmpt4g.mm"
include "3expia.mm"
include "vtocl2gaf.mm"
include "csbcom.mm"
include "eleq1i.mm"
include "eqeq2i.mm"
include "3imtr4g.mm"
include "syl5.mm"
include "3impia.mm"

theorem ovmpt2s
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cV: class V
  assume ovmpt2s.3: |- F = ( x e. C , y e. D |-> R )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  assert |- ( ( A e. C /\ B e. D /\ [_ A / x ]_ [_ B / y ]_ R e. V ) -> ( A F B ) = [_ A / x ]_ [_ B / y ]_ R )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    vx
    cA
    vy
    cB
    cR
    csb
    csb
    #
    cV
    wcel
    #
    cA
    cB
    cF
    co
    #
    @2
    wceq
    #
    @3
    @2
    cvv
    wcel
    #
    @0
    @1
    wa
    #
    @5
    @2
    cV
    elex
    @7
    vy
    cB
    vx
    cA
    cR
    csb
    #
    csb
    #
    cvv
    wcel
    #
    @4
    @9
    wceq
    #
    @6
    @5
    cR
    cvv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    cR
    wceq
    #
    wi
    @8
    cvv
    wcel
    #
    cA
    @14
    cF
    co
    #
    @8
    wceq
    #
    wi
    @10
    @11
    wi
    vx
    vy
    cA
    cB
    cC
    cD
    vx
    cA
    nfcv
    #
    vy
    cA
    nfcv
    #
    vy
    cB
    nfcv
    #
    @17
    @19
    vx
    vx
    @8
    cvv
    vx
    cA
    cR
    nfcsb1v
    #
    nfel1
    vx
    @18
    @8
    vx
    cA
    @14
    cF
    @20
    vx
    cF
    vx
    vy
    cC
    cD
    cR
    cmpt2
    #
    ovmpt2s.3
    vx
    vy
    cC
    cD
    cR
    nfmpt21
    nfcxfr
    vx
    @14
    nfcv
    nfov
    @23
    nfeq
    nfim
    @10
    @11
    vy
    vy
    @9
    cvv
    vy
    cB
    @8
    nfcsb1v
    #
    nfel1
    vy
    @4
    @9
    vy
    cA
    cB
    cF
    @21
    vy
    cF
    @24
    ovmpt2s.3
    vx
    vy
    cC
    cD
    cR
    nfmpt22
    nfcxfr
    @22
    nfov
    @25
    nfeq
    nfim
    @13
    cA
    wceq
    #
    @12
    @17
    @16
    @19
    @26
    cR
    @8
    cvv
    vx
    cA
    cR
    csbeq1a
    #
    eleq1d
    @26
    @15
    @18
    cR
    @8
    @13
    cA
    @14
    cF
    oveq1
    @27
    eqeq12d
    imbi12d
    @14
    cB
    wceq
    #
    @17
    @10
    @19
    @11
    @28
    @8
    @9
    cvv
    vy
    cB
    @8
    csbeq1a
    #
    eleq1d
    @28
    @18
    @4
    @8
    @9
    @14
    cB
    cA
    cF
    oveq2
    @29
    eqeq12d
    imbi12d
    @13
    cC
    wcel
    @14
    cD
    wcel
    @12
    @16
    vx
    vy
    cC
    cD
    cR
    cF
    cvv
    ovmpt2s.3
    ovmpt4g
    3expia
    vtocl2gaf
    @2
    @9
    cvv
    vx
    vy
    cA
    cB
    cR
    csbcom
    #
    eleq1i
    @2
    @9
    @4
    @30
    eqeq2i
    3imtr4g
    syl5
    3impia
end
