include "cvv.mm"
include "wcel.mm"
include "cixp.mm"
include "cmap.mm"
include "co.mm"
include "wceq.mm"
include "ixpconstg.mm"
include "mp2an.mm"

theorem ixpconst
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  assume ixpconst.1: |- A e. _V
  assume ixpconst.2: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint f x
  disjoint A f
  disjoint B f
  assert |- X_ x e. A B = ( B ^m A )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    vx
    cA
    cB
    cixp
    cB
    cA
    cmap
    co
    wceq
    ixpconst.1
    ixpconst.2
    vx
    cA
    cB
    cvv
    cvv
    ixpconstg
    mp2an
end
