include "wreu.mm"
include "crab.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "reusn.mm"
include "en1.mm"
include "bitr4i.mm"

theorem reuen1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vy: setvar y

  disjoint A x
  disjoint f x
  disjoint x y
  disjoint f y
  disjoint A f
  disjoint A y
  disjoint ph y
  assert |- ( E! x e. A ph <-> { x e. A | ph } ~~ 1o )

  proof
    wph
    vx
    cA
    wreu
    wph
    vx
    cA
    crab
    #
    vy
    cv
    csn
    wceq
    vy
    wex
    @0
    c1o
    cen
    wbr
    wph
    vx
    vy
    cA
    reusn
    vy
    @0
    en1
    bitr4i
end
