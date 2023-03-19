include "cmpt2.mm"
include "eqid.mm"
include "mpt2exg.mm"

theorem mpt2exga
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( A e. V /\ B e. W ) -> ( x e. A , y e. B |-> C ) e. _V )

  proof
    vx
    vy
    cA
    cB
    cC
    cV
    cW
    vx
    vy
    cA
    cB
    cC
    cmpt2
    #
    @0
    eqid
    mpt2exg
end
