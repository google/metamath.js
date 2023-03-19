include "wtru.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wreu.mm"
include "tru.mm"
include "adantl.mm"
include "wb.mm"
include "3adant1.mm"
include "reuhypd.mm"
include "mpan.mm"

theorem reuhyp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume reuhyp.1: |- ( x e. C -> B e. C )
  assume reuhyp.2: |- ( ( x e. C /\ y e. C ) -> ( x = A <-> y = B ) )

  disjoint B y
  disjoint C y
  disjoint x y
  assert |- ( x e. C -> E! y e. C x = A )

  proof
    wtru
    vx
    cv
    #
    cC
    wcel
    #
    @0
    cA
    wceq
    #
    vy
    cC
    wreu
    tru
    wtru
    vx
    vy
    cA
    cB
    cC
    @1
    cB
    cC
    wcel
    wtru
    reuhyp.1
    adantl
    @1
    vy
    cv
    #
    cC
    wcel
    @2
    @3
    cB
    wceq
    wb
    wtru
    reuhyp.2
    3adant1
    reuhypd
    mpan
end
