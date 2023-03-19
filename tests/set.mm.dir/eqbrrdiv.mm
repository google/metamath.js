include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "df-br.mm"
include "3bitr3g.mm"
include "eqrelrdv.mm"

theorem eqbrrdiv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume eqbrrdiv.1: |- Rel A
  assume eqbrrdiv.2: |- Rel B
  assume eqbrrdiv.3: |- ( ph -> ( x A y <-> x B y ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A = B )

  proof
    wph
    vx
    vy
    cA
    cB
    eqbrrdiv.1
    eqbrrdiv.2
    wph
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
    eqbrrdiv.3
    @0
    @1
    cA
    df-br
    @0
    @1
    cB
    df-br
    3bitr3g
    eqrelrdv
end
