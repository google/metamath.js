include "cab.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wb.mm"
include "bj-issetwt.mm"
include "mpg.mm"

theorem bj-issetw
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume bj-issetw.1: |- ph

  disjoint A y
  assert |- ( A e. { x | ph } <-> E. y y = A )

  proof
    wph
    cA
    wph
    vx
    cab
    wcel
    vy
    cv
    cA
    wceq
    vy
    wex
    wb
    vx
    wph
    vx
    vy
    cA
    bj-issetwt
    bj-issetw.1
    mpg
end
