include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "co.mm"
include "fmpt2.mm"
include "fovrn.mm"
include "syl3an1b.mm"

theorem ovmpt2elrn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cO: class O
  let cX: class X
  let cY: class Y
  assume ovmpt2elrn.o: |- O = ( x e. A , y e. B |-> C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint M x
  disjoint M y
  assert |- ( ( A. x e. A A. y e. B C e. M /\ X e. A /\ Y e. B ) -> ( X O Y ) e. M )

  proof
    cC
    cM
    wcel
    vy
    cB
    wral
    vx
    cA
    wral
    cA
    cB
    cxp
    cM
    cO
    wf
    cX
    cA
    wcel
    cY
    cB
    wcel
    cX
    cY
    cO
    co
    cM
    wcel
    vx
    vy
    cA
    cB
    cC
    cM
    cO
    ovmpt2elrn.o
    fmpt2
    cX
    cY
    cM
    cA
    cB
    cO
    fovrn
    syl3an1b
end
