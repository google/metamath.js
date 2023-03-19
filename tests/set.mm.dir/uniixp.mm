include "cixp.mm"
include "ciun.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wf.mm"
include "ixpf.mm"
include "fssxp.mm"
include "syl.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"
include "sspwuni.mm"
include "mpbi.mm"

theorem uniixp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cC: class C

  disjoint A x
  disjoint f x
  disjoint A f
  disjoint B f
  disjoint F x
  disjoint C f
  assert |- U. X_ x e. A B C_ ( A X. U_ x e. A B )

  proof
    vx
    cA
    cB
    cixp
    #
    cA
    vx
    cA
    cB
    ciun
    #
    cxp
    #
    cpw
    #
    wss
    @0
    cuni
    @2
    wss
    vf
    @0
    @3
    vf
    cv
    #
    @0
    wcel
    #
    @4
    @2
    wss
    #
    @4
    @3
    wcel
    @5
    cA
    @1
    @4
    wf
    @6
    vx
    cA
    cB
    @4
    ixpf
    cA
    @1
    @4
    fssxp
    syl
    vf
    @2
    selpw
    sylibr
    ssriv
    @0
    @2
    sspwuni
    mpbi
end
