include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "cmpt2.mm"
include "rgenw.mm"
include "eqid.mm"
include "mpt2exxg.mm"
include "mp2an.mm"

theorem mpt2ex
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume mpt2ex.1: |- A e. _V
  assume mpt2ex.2: |- B e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  assert |- ( x e. A , y e. B |-> C ) e. _V

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    vx
    vy
    cA
    cB
    cC
    cmpt2
    #
    cvv
    wcel
    mpt2ex.1
    @0
    vx
    cA
    mpt2ex.2
    rgenw
    vx
    vy
    cA
    cB
    cC
    cvv
    cvv
    @1
    @1
    eqid
    mpt2exxg
    mp2an
end
