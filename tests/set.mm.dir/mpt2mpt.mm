include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "iunxpconst.mm"
include "mpteq1.mm"
include "ax-mp.mm"
include "mpt2mptx.mm"
include "eqtr3i.mm"

theorem mpt2mpt
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  assume mpt2mpt.1: |- ( z = <. x , y >. -> C = D )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint D z
  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint D w
  assert |- ( z e. ( A X. B ) |-> C ) = ( x e. A , y e. B |-> D )

  proof
    vz
    vx
    cA
    vx
    cv
    csn
    cB
    cxp
    ciun
    #
    cC
    cmpt
    #
    vz
    cA
    cB
    cxp
    #
    cC
    cmpt
    #
    vx
    vy
    cA
    cB
    cD
    cmpt2
    @0
    @2
    wceq
    @1
    @3
    wceq
    vx
    cA
    cB
    iunxpconst
    vz
    @0
    @2
    cC
    mpteq1
    ax-mp
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    mpt2mpt.1
    mpt2mptx
    eqtr3i
end
