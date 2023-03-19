include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "n0i.mm"
include "cdm.mm"
include "dmmptss.mm"
include "sseli.mm"
include "ndmfv.mm"
include "nsyl4.mm"
include "syl.mm"

theorem mptrcl
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cI: class I
  let cX: class X
  assume mptrcl.1: |- F = ( x e. A |-> B )

  disjoint A x
  assert |- ( I e. ( F ` X ) -> X e. A )

  proof
    cI
    cX
    cF
    cfv
    #
    wcel
    @0
    c0
    wceq
    #
    wn
    cX
    cA
    wcel
    #
    @0
    cI
    n0i
    cX
    cF
    cdm
    #
    wcel
    @2
    @1
    @3
    cA
    cX
    vx
    cA
    cB
    cF
    mptrcl.1
    dmmptss
    sseli
    cX
    cF
    ndmfv
    nsyl4
    syl
end
