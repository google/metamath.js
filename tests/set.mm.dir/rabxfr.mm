include "wtru.mm"
include "wcel.mm"
include "crab.mm"
include "wb.mm"
include "tru.mm"
include "cv.mm"
include "adantl.mm"
include "rabxfrd.mm"
include "mpan.mm"

theorem rabxfr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rabxfr.1: |- F/_ y B
  assume rabxfr.2: |- F/_ y C
  assume rabxfr.3: |- ( y e. D -> A e. D )
  assume rabxfr.4: |- ( x = A -> ( ph <-> ps ) )
  assume rabxfr.5: |- ( y = B -> A = C )

  disjoint A x
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint ph y
  disjoint ps x
  assert |- ( B e. D -> ( C e. { x e. D | ph } <-> B e. { y e. D | ps } ) )

  proof
    wtru
    cB
    cD
    wcel
    cC
    wph
    vx
    cD
    crab
    wcel
    cB
    wps
    vy
    cD
    crab
    wcel
    wb
    tru
    wtru
    wph
    wps
    vx
    vy
    cA
    cB
    cC
    cD
    rabxfr.1
    rabxfr.2
    vy
    cv
    cD
    wcel
    cA
    cD
    wcel
    wtru
    rabxfr.3
    adantl
    rabxfr.4
    rabxfr.5
    rabxfrd
    mpan
end
