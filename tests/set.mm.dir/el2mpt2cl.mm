include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "co.mm"
include "csb.mm"
include "el2mpt2csbcl.mm"
include "simpl.mm"
include "cv.mm"
include "wceq.mm"
include "simplr.mm"
include "simpld.mm"
include "adantll.mm"
include "csbied.mm"
include "eleq2d.mm"
include "simprd.mm"
include "anbi12d.mm"
include "biimpd.mm"
include "imdistani.mm"
include "syl6.mm"

theorem el2mpt2cl
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  assume el2mpt2cl.o: |- O = ( x e. A , y e. B |-> ( s e. C , t e. D |-> E ) )
  assume el2mpt2cl.e: |- ( ( x = X /\ y = Y ) -> ( C = F /\ D = G ) )

  disjoint A s
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint B s
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint C s
  disjoint C t
  disjoint D s
  disjoint D t
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint U x
  disjoint U y
  disjoint V x
  disjoint V y
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint Y s
  disjoint Y t
  disjoint Y x
  disjoint Y y
  assert |- ( A. x e. A A. y e. B ( C e. U /\ D e. V ) -> ( W e. ( S ( X O Y ) T ) -> ( ( X e. A /\ Y e. B ) /\ ( S e. F /\ T e. G ) ) ) )

  proof
    cC
    cU
    wcel
    cD
    cV
    wcel
    wa
    vy
    cB
    wral
    vx
    cA
    wral
    cW
    cS
    cT
    cX
    cY
    cO
    co
    co
    wcel
    cX
    cA
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cS
    vx
    cX
    vy
    cY
    cC
    csb
    #
    csb
    #
    wcel
    #
    cT
    vx
    cX
    vy
    cY
    cD
    csb
    #
    csb
    #
    wcel
    #
    wa
    #
    wa
    @2
    cS
    cF
    wcel
    #
    cT
    cG
    wcel
    #
    wa
    #
    wa
    vx
    vy
    vt
    cA
    cB
    cC
    cD
    cS
    cT
    cU
    cE
    cO
    cV
    cW
    cX
    cY
    vs
    el2mpt2cl.o
    el2mpt2csbcl
    @2
    @9
    @12
    @2
    @9
    @12
    @2
    @5
    @10
    @8
    @11
    @2
    @4
    cF
    cS
    @2
    vx
    cX
    @3
    cF
    cA
    @0
    @1
    simpl
    #
    @2
    vx
    cv
    cX
    wceq
    #
    wa
    #
    vy
    cY
    cC
    cF
    cB
    @0
    @1
    @14
    simplr
    #
    @14
    vy
    cv
    cY
    wceq
    #
    cC
    cF
    wceq
    #
    @2
    @14
    @17
    wa
    #
    @18
    cD
    cG
    wceq
    #
    el2mpt2cl.e
    simpld
    adantll
    csbied
    csbied
    eleq2d
    @2
    @7
    cG
    cT
    @2
    vx
    cX
    @6
    cG
    cA
    @13
    @15
    vy
    cY
    cD
    cG
    cB
    @16
    @14
    @17
    @20
    @2
    @19
    @18
    @20
    el2mpt2cl.e
    simprd
    adantll
    csbied
    csbied
    eleq2d
    anbi12d
    biimpd
    imdistani
    syl6
end
