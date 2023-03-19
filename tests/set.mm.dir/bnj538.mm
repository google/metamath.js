include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "wsbc.mm"
include "wb.mm"
include "sbcralg.mm"
include "ax-mp.mm"

theorem bnj538
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume bnj538.1: |- A e. _V

  disjoint A x
  disjoint B y
  disjoint x y
  assert |- ( [. A / y ]. A. x e. B ph <-> A. x e. B [. A / y ]. ph )

  proof
    cA
    cvv
    wcel
    wph
    vx
    cB
    wral
    vy
    cA
    wsbc
    wph
    vy
    cA
    wsbc
    vx
    cB
    wral
    wb
    bnj538.1
    wph
    vy
    vx
    cA
    cB
    cvv
    sbcralg
    ax-mp
end
