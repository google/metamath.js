include "cxp.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "nfcri.mm"
include "cop.mm"
include "wceq.mm"
include "eleq2d.mm"
include "rexxpf.mm"
include "eliun.mm"
include "rexbii.mm"
include "bitri.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iunxpf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  assume iunxpf.1: |- F/_ y C
  assume iunxpf.2: |- F/_ z C
  assume iunxpf.3: |- F/_ x D
  assume iunxpf.4: |- ( x = <. y , z >. -> C = D )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint w z
  disjoint B w
  disjoint C w
  disjoint D w
  assert |- U_ x e. ( A X. B ) C = U_ y e. A U_ z e. B D

  proof
    vw
    vx
    cA
    cB
    cxp
    #
    cC
    ciun
    #
    vy
    cA
    vz
    cB
    cD
    ciun
    #
    ciun
    #
    vw
    cv
    #
    cC
    wcel
    #
    vx
    @0
    wrex
    @4
    cD
    wcel
    #
    vz
    cB
    wrex
    #
    vy
    cA
    wrex
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    #
    @5
    @6
    vx
    vy
    vz
    cA
    cB
    vy
    vw
    cC
    iunxpf.1
    nfcri
    vz
    vw
    cC
    iunxpf.2
    nfcri
    vx
    vw
    cD
    iunxpf.3
    nfcri
    vx
    cv
    vy
    cv
    vz
    cv
    cop
    wceq
    cC
    cD
    @4
    iunxpf.4
    eleq2d
    rexxpf
    vx
    @4
    @0
    cC
    eliun
    @9
    @4
    @2
    wcel
    #
    vy
    cA
    wrex
    @8
    vy
    @4
    cA
    @2
    eliun
    @10
    @7
    vy
    cA
    vz
    @4
    cB
    cD
    eliun
    rexbii
    bitri
    3bitr4i
    eqriv
end
