include "wral.mm"
include "wb.mm"
include "wtru.mm"
include "cv.mm"
include "wcel.mm"
include "adantl.mm"
include "wceq.mm"
include "wrex.mm"
include "ralxfrd.mm"
include "trud.mm"

theorem ralxfr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume ralxfr.1: |- ( y e. C -> A e. B )
  assume ralxfr.2: |- ( x e. B -> E. y e. C x = A )
  assume ralxfr.3: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint ph y
  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  assert |- ( A. x e. B ph <-> A. y e. C ps )

  proof
    wph
    vx
    cB
    wral
    wps
    vy
    cC
    wral
    wb
    wtru
    wph
    wps
    vx
    vy
    cA
    cB
    cC
    vy
    cv
    cC
    wcel
    cA
    cB
    wcel
    wtru
    ralxfr.1
    adantl
    vx
    cv
    #
    cB
    wcel
    @0
    cA
    wceq
    #
    vy
    cC
    wrex
    wtru
    ralxfr.2
    adantl
    @1
    wph
    wps
    wb
    wtru
    ralxfr.3
    adantl
    ralxfrd
    trud
end
