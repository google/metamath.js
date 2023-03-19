include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "cxp.mm"
include "wfn.mm"
include "elex.mm"
include "2ralimi.mm"
include "wf.mm"
include "fmpt2.mm"
include "dffn2.mm"
include "bitr4i.mm"
include "sylib.mm"

theorem fnmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cD: class D
  assume fmpt2.1: |- F = ( x e. A , y e. B |-> C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint D x
  disjoint D y
  assert |- ( A. x e. A A. y e. B C e. V -> F Fn ( A X. B ) )

  proof
    cC
    cV
    wcel
    #
    vy
    cB
    wral
    vx
    cA
    wral
    cC
    cvv
    wcel
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    cF
    cA
    cB
    cxp
    #
    wfn
    #
    @0
    @1
    vx
    vy
    cA
    cB
    cC
    cV
    elex
    2ralimi
    @2
    @3
    cvv
    cF
    wf
    @4
    vx
    vy
    cA
    cB
    cC
    cvv
    cF
    fmpt2.1
    fmpt2
    @3
    cF
    dffn2
    bitr4i
    sylib
end
