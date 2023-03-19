include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "df-br.mm"
include "3bitr3i.mm"
include "eqrelriiv.mm"

theorem eqbrriv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume eqbrriv.1: |- Rel A
  assume eqbrriv.2: |- Rel B
  assume eqbrriv.3: |- ( x A y <-> x B y )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- A = B

  proof
    vx
    vy
    cA
    cB
    eqbrriv.1
    eqbrriv.2
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    @0
    @1
    cB
    wbr
    @0
    @1
    cop
    #
    cA
    wcel
    @2
    cB
    wcel
    eqbrriv.3
    @0
    @1
    cA
    df-br
    @0
    @1
    cB
    df-br
    3bitr3i
    eqrelriiv
end
