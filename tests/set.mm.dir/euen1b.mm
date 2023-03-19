include "cv.mm"
include "wcel.mm"
include "weu.mm"
include "cab.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "euen1.mm"
include "abid2.mm"
include "breq1i.mm"
include "bitr2i.mm"

theorem euen1b
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vy: setvar y
  let wph: wff ph

  disjoint A x
  disjoint f x
  disjoint x y
  disjoint f y
  disjoint A f
  disjoint A y
  disjoint ph y
  assert |- ( A ~~ 1o <-> E! x x e. A )

  proof
    vx
    cv
    cA
    wcel
    #
    vx
    weu
    @0
    vx
    cab
    #
    c1o
    cen
    wbr
    cA
    c1o
    cen
    wbr
    @0
    vx
    euen1
    @1
    cA
    c1o
    cen
    vx
    cA
    abid2
    breq1i
    bitr2i
end
