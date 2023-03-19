include "cgru.mm"
include "wcel.mm"
include "wrex.mm"
include "ciin.mm"
include "nfv.mm"
include "nfii1.mm"
include "nfel1.mm"
include "cv.mm"
include "wss.mm"
include "iinss2.mm"
include "gruss.mm"
include "syl3an3.mm"
include "3exp.mm"
include "com23.mm"
include "rexlimd.mm"
include "imp.mm"

theorem gruiin
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cU: class U
  let vy: setvar y
  let cF: class F

  disjoint U x
  disjoint A x
  disjoint U y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F x
  disjoint F y
  assert |- ( ( U e. Univ /\ E. x e. A B e. U ) -> |^|_ x e. A B e. U )

  proof
    cU
    cgru
    wcel
    #
    cB
    cU
    wcel
    #
    vx
    cA
    wrex
    vx
    cA
    cB
    ciin
    #
    cU
    wcel
    #
    @0
    @1
    @3
    vx
    cA
    @0
    vx
    nfv
    vx
    @2
    cU
    vx
    cA
    cB
    nfii1
    nfel1
    @0
    @1
    vx
    cv
    cA
    wcel
    #
    @3
    @0
    @1
    @4
    @3
    @4
    @0
    @1
    @2
    cB
    wss
    @3
    vx
    cA
    cB
    iinss2
    cB
    @2
    cU
    gruss
    syl3an3
    3exp
    com23
    rexlimd
    imp
end
