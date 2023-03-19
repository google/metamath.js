include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cvv.mm"
include "wa.mm"
include "elex.mm"
include "cv.mm"
include "wi.mm"
include "nfel1.mm"
include "cmpt2.mm"
include "nfmpt21.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nfov.mm"
include "nfeq.mm"
include "nfim.mm"
include "nfmpt22.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "ovmpt4g.mm"
include "3expia.mm"
include "vtocl2gaf.mm"
include "syl5.mm"
include "3impia.mm"

theorem ov2gf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  assume ov2gf.a: |- F/_ x A
  assume ov2gf.c: |- F/_ y A
  assume ov2gf.d: |- F/_ y B
  assume ov2gf.1: |- F/_ x G
  assume ov2gf.2: |- F/_ y S
  assume ov2gf.3: |- ( x = A -> R = G )
  assume ov2gf.4: |- ( y = B -> G = S )
  assume ov2gf.5: |- F = ( x e. C , y e. D |-> R )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  assert |- ( ( A e. C /\ B e. D /\ S e. H ) -> ( A F B ) = S )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    cS
    cH
    wcel
    #
    cA
    cB
    cF
    co
    #
    cS
    wceq
    #
    @2
    cS
    cvv
    wcel
    #
    @0
    @1
    wa
    @4
    cS
    cH
    elex
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
    cG
    cvv
    wcel
    #
    cA
    @8
    cF
    co
    #
    cG
    wceq
    #
    wi
    @5
    @4
    wi
    vx
    vy
    cA
    cB
    cC
    cD
    ov2gf.a
    ov2gf.c
    ov2gf.d
    @11
    @13
    vx
    vx
    cG
    cvv
    ov2gf.1
    nfel1
    vx
    @12
    cG
    vx
    cA
    @8
    cF
    ov2gf.a
    vx
    cF
    vx
    vy
    cC
    cD
    cR
    cmpt2
    #
    ov2gf.5
    vx
    vy
    cC
    cD
    cR
    nfmpt21
    nfcxfr
    vx
    @8
    nfcv
    nfov
    ov2gf.1
    nfeq
    nfim
    @5
    @4
    vy
    vy
    cS
    cvv
    ov2gf.2
    nfel1
    vy
    @3
    cS
    vy
    cA
    cB
    cF
    ov2gf.c
    vy
    cF
    @14
    ov2gf.5
    vx
    vy
    cC
    cD
    cR
    nfmpt22
    nfcxfr
    ov2gf.d
    nfov
    ov2gf.2
    nfeq
    nfim
    @7
    cA
    wceq
    #
    @6
    @11
    @10
    @13
    @15
    cR
    cG
    cvv
    ov2gf.3
    eleq1d
    @15
    @9
    @12
    cR
    cG
    @7
    cA
    @8
    cF
    oveq1
    ov2gf.3
    eqeq12d
    imbi12d
    @8
    cB
    wceq
    #
    @11
    @5
    @13
    @4
    @16
    cG
    cS
    cvv
    ov2gf.4
    eleq1d
    @16
    @12
    @3
    cG
    cS
    @8
    cB
    cA
    cF
    oveq2
    ov2gf.4
    eqeq12d
    imbi12d
    @7
    cC
    wcel
    @8
    cD
    wcel
    @6
    @10
    vx
    vy
    cC
    cD
    cR
    cF
    cvv
    ov2gf.5
    ovmpt4g
    3expia
    vtocl2gaf
    syl5
    3impia
end
